# metrics_codesys.py
# Build OWLalyze metrics from a Codesys-parsed project dict.
import json
import logging
import re
from pathlib import Path
from collections import defaultdict, deque

logger = logging.getLogger("owlalyze.metrics.codesys")

# ---------------------- helpers ----------------------

def _round4(x: float) -> float:
    try:
        return float(f"{x:.4f}")
    except Exception:
        return 0.0

def _safe_list(x):
    return x if isinstance(x, list) else []

def _tokenize(s: str) -> list[str]:
    if not s:
        return []
    return re.findall(r"[A-Za-z0-9_\.]{2,}", s)

def _base_tag(name: str) -> str:
    if not name:
        return ""
    return re.split(r"[\.\[]", name, 1)[0]

def _get_program_pous(proj):
    """Return list of POUs with pouType == 'program' (fallback: all POUs)."""
    pous = _safe_list(proj.get("pous"))
    progs = [p for p in pous if (p.get("pouType") or "").lower() == "program"]
    return progs if progs else pous

def _collect_all_vars_from_interface(iface: dict) -> list[dict]:
    buckets = [
        "localVars","tempVars","inputVars","outputVars",
        "inOutVars","externalVars","globalVars","accessVars"
    ]
    out = []
    for b in buckets:
        out.extend(_safe_list(iface.get(b)))
    return out

def _build_var_index(proj):
    """Index variable meta by name: {name: {type, physical, phyOutIn, documentation, address}}."""
    idx = {}
    for pou in _safe_list(proj.get("pous")):
        iface = pou.get("interface") or {}
        for v in _collect_all_vars_from_interface(iface):
            name = v.get("name")
            if not name:
                continue
            idx[name] = {
                "type": v.get("type"),
                "physical": bool(v.get("physical")),
                "phyOutIn": v.get("phyOutIn"),
                "documentation": v.get("documentation") or "",
                "address": v.get("address") or ""
            }
    return idx

# ------- Ladder (PLCopenXML) extraction from ldComponentLookup --------

# We prefer ldComponentLookup (complete, keyed by localId). If absent, fallback to ldComponents list.

def _get_components(pou):
    lk = pou.get("ldComponentLookup")
    if isinstance(lk, dict) and lk:
        # Normalize to {int localId: component dict}
        cmap = {}
        for k, v in lk.items():
            try:
                lid = int(k)
            except Exception:
                continue
            cmap[lid] = v
        return cmap
    # Fallback: list
    cmap = {}
    for comp in _safe_list(pou.get("ldComponents")):
        try:
            lid = int(comp.get("localId"))
        except Exception:
            continue
        cmap[lid] = comp
    return cmap

_var_pat = re.compile(r"<variable>(.*?)</variable>", re.IGNORECASE | re.DOTALL)
_neg_pat = re.compile(r'\bnegated="(true|false)"', re.IGNORECASE)
_type_pat = re.compile(r'\btypeName="([A-Za-z0-9_]+)"')
_expr_pat = re.compile(r"<expression>(.*?)</expression>", re.IGNORECASE | re.DOTALL)

def _parse_contact_info(structure: str):
    """Returns (name:str|None, negated:bool|None)."""
    if not structure:
        return None, None
    name = None
    m = _var_pat.search(structure)
    if m:
        name = (m.group(1) or "").strip()
    neg = None
    m2 = _neg_pat.search(structure)
    if m2:
        neg = (m2.group(1).lower() == "true")
    return name, neg

def _parse_coil_var(structure: str):
    if not structure:
        return None
    m = _var_pat.search(structure)
    return (m.group(1) or "").strip() if m else None

def _parse_block_type(structure: str):
    if not structure:
        return None
    m = _type_pat.search(structure)
    return m.group(1) if m else None

def _parse_expressions(structure: str) -> list[str]:
    if not structure:
        return []
    return [ (m or "").strip() for m in _expr_pat.findall(structure) ]

def _conn_in_ids(comp: dict) -> list[int]:
    ids = []
    for c in _safe_list(comp.get("connectionsIn")):
        try:
            rid = int(c.get("refLocalId"))
            ids.append(rid)
        except Exception:
            pass
    return ids

def _gather_comments_in_pou(pou) -> list[str]:
    texts = []
    cmap = _get_components(pou)
    for c in cmap.values():
        if (c.get("type") or "").lower() == "comment":
            s = c.get("structure") or ""
            inner = re.sub(r"<.*?>", "", s)  # remove tags loosely
            inner = inner.strip()
            if inner:
                texts.append(inner)
    return texts

# ---------------------- metric building blocks ----------------------

COMPARATORS = {"LT","LE","GE","GT","EQ","NE","LIMIT","MIN","MAX"}  # PLCopen block names for compare-like ops
TIMER_BLOCKS = {"TON","TOF","TP"}
COUNTER_BLOCKS = {"CTU","CTD","CTUD"}

ACTUATOR_KW = ["pump", "motor", "valve", "heater", "fan", "conveyor", "actuator", "relay"]
INPUT_KW = ["ai", "input", "sensor", "switch", "pb", "button", "estop", "e-stop", "limit", "ls", "pv", "di", "state"]
SAFETY_KW = ["estop", "e-stop", "trip", "safe", "safety", "esd", "interlock", "guard", "fault", "alarm"]
CONFIG_KW = ["cfg", "config", "parameter", "param", "mode", "recipe", "setup", "enable"]
PID_KW = ["pid", "kp", "ki", "kd"]
SP_KW = ["setpoint", "sp", ".sp", "_sp"]
SCALE_KW = ["scale", "scaled", "scaling", "limit", "normalize", "range"]
ALARM_KW = ["alarm", "alm"]
INTERLOCK_KW = ["interlock", "trip", "esd", "estop", "e-stop", "permissive"]
PSA_KW = ["hazop", "lopa", "sil", "sif", "pha", "srs"]

DOMAIN_TERMS = ["pump","pid","motor","valve","heater","tank","level","pressure",
                "flow","temperature","alarm","scale","counter","timer","sensor",
                "actuator","conveyor","mixer"]

def _contains_any(s: str, kws) -> bool:
    ls = (s or "").lower()
    return any(k in ls for k in kws)

def _build_rungs_from_ld(pou):
    """
    Build rung-like data per coil by recursively walking connectionsIn.
    Returns list of dicts:
      {
        "coil_id": int,
        "coil_var": str|None,
        "contacts": [(var, negated:bool|None)],
        "blocks": [block_type_name],
        "expressions": [expr strings],
      }
    """
    cmap = _get_components(pou)
    # Find coil components
    coil_ids = [lid for lid, c in cmap.items() if (c.get("type") or "").lower() == "coil"]
    rungs = []
    for coil in coil_ids:
        ccoil = cmap.get(coil, {})
        coil_var = _parse_coil_var(ccoil.get("structure") or "")
        seen = set()
        q = deque([coil])
        contacts = []
        blocks = []
        exprs = []
        while q:
            nid = q.popleft()
            if nid in seen:
                continue
            seen.add(nid)
            comp = cmap.get(nid, {})
            ctype = (comp.get("type") or "").lower()
            s = comp.get("structure") or ""

            if ctype == "contact":
                name, neg = _parse_contact_info(s)
                if name:
                    contacts.append((name, neg))
            elif ctype == "block":
                bt = _parse_block_type(s)
                if bt:
                    blocks.append(bt.upper())
                exprs.extend(_parse_expressions(s))
            elif ctype in ("invariable", "coil"):
                exprs.extend(_parse_expressions(s))
            # Continue walking upstream
            for up in _conn_in_ids(comp):
                q.append(up)
        rungs.append({
            "coil_id": coil,
            "coil_var": coil_var,
            "contacts": contacts,
            "blocks": blocks,
            "expressions": exprs,
        })
    return rungs

def _count_lines_codesys(proj):
    """
    Approximate line count:
      - 1 per ldComponent entry
      - + number of non-empty documentation lines
      - + 1 per expression found in ladder blocks/vars
    """
    lines = 0
    for pou in _get_program_pous(proj):
        comps = _get_components(pou)
        lines += len(comps)
        # docs
        iface = pou.get("interface") or {}
        for v in _collect_all_vars_from_interface(iface):
            if v.get("documentation"):
                lines += max(1, v["documentation"].count("\n") + 1)
        # expressions
        for c in comps.values():
            s = c.get("structure") or ""
            exprs = _parse_expressions(s)
            lines += len([e for e in exprs if (e or "").strip()])
    return lines or 0

def _collect_program_names(proj):
    return [p.get("name") for p in _get_program_pous(proj) if p.get("name")]

def _collect_languages(proj):
    langs = set()
    total = 0
    rll_cnt = 0
    for p in _get_program_pous(proj):
        bt = p.get("bodyType")
        if bt:
            langs.add(bt)
            total += 1
            if bt.upper() in ("LD","RLL","LADDER"):
                rll_cnt += 1
    rll_pct = (rll_cnt / total) if total else 0.0
    return langs, total, rll_pct

def _collect_tag_counts(proj):
    ctrl = 0
    prog = 0
    for p in _safe_list(proj.get("pous")):
        iface = p.get("interface") or {}
        # "globalVars" we treat as controller-scoped for Codesys
        ctrl += len(_safe_list(iface.get("globalVars")))
        # Everything else is program-scoped
        prog += len(_collect_all_vars_from_interface(iface)) - len(_safe_list(iface.get("globalVars")))
    return ctrl + prog, ctrl, prog

def _iter_all_text(proj):
    # Names, docs, expressions in ladder, task settings text-ish
    # Project-level meta
    for k in ("companyName","contentDescription","organization","author","language","name"):
        v = proj.get(k)
        if v: yield v
    # instances/task settings
    for cfg in _safe_list(proj.get("instances",{}).get("configurations")):
        for res in _safe_list(cfg.get("resources")):
            for t in _safe_list(res.get("tasks")):
                yield t.get("name") or ""
                ts = t.get("taskSettings") or {}
                for tk, tv in ts.items():
                    if isinstance(tv, dict):
                        for vv in tv.values():
                            if isinstance(vv, str):
                                yield vv
                    elif isinstance(tv, str):
                        yield tv
    # POU names and bodies
    for p in _safe_list(proj.get("pous")):
        if p.get("name"): yield p["name"]
        iface = p.get("interface") or {}
        for v in _collect_all_vars_from_interface(iface):
            for k in ("name","type","documentation","address","phyOutIn"):
                if v.get(k):
                    yield str(v[k])
        comps = _get_components(p)
        for c in comps.values():
            s = c.get("structure") or ""
            if s:
                # strip tags to free text-ish
                yield re.sub(r"<.*?>", " ", s)

def _psa_terms(proj):
    found_psa, found_alarm, found_inter = set(), set(), set()

    def sift(s):
        if not s:
            return
        ls = s.lower()
        if any(k in ls for k in PSA_KW):
            found_psa.add(s)
        if any(k in ls for k in ALARM_KW):
            found_alarm.add(s)
        if any(k in ls for k in INTERLOCK_KW):
            found_inter.add(s)

    # variable names & docs
    for p in _safe_list(proj.get("pous")):
        iface = p.get("interface") or {}
        for v in _collect_all_vars_from_interface(iface):
            sift(v.get("name"))
            sift(v.get("documentation"))
    # ladder components text
    for p in _get_program_pous(proj):
        comps = _get_components(p)
        for c in comps.values():
            s = c.get("structure") or ""
            for tok in _tokenize(re.sub(r"<.*?>", " ", s)):
                sift(tok)

    groups = []
    if found_psa:
        groups.append(",".join(sorted(found_psa)))
    if found_alarm:
        groups.append(",".join(sorted(found_alarm)))
    if found_inter:
        groups.append(",".join(sorted(found_inter)))
    return len(found_psa | found_alarm | found_inter), "|".join(groups)

def _terms_catalog(proj):
    terms = set()
    for s in _iter_all_text(proj):
        ls = (s or "").lower()
        for t in DOMAIN_TERMS:
            if t in ls:
                terms.add(t)
    return ",".join(sorted(terms))

def _discoverability(proj):
    token_count = 0
    for s in _iter_all_text(proj):
        token_count += len(re.findall(r"[A-Za-z]{3,}", s or ""))
    lines = _count_lines_codesys(proj)
    avg = (token_count / lines) if lines else 0.0
    # breadth: fraction of POUs with any comments/docs or non-empty expressions
    with_context = 0
    pous = _get_program_pous(proj)
    for p in pous:
        has = False
        iface = p.get("interface") or {}
        if any((v.get("documentation") or "").strip() for v in _collect_all_vars_from_interface(iface)):
            has = True
        if not has:
            if any(_gather_comments_in_pou(p)):
                has = True
        if not has:
            comps = _get_components(p)
            for c in comps.values():
                if any((e or "").strip() for e in _parse_expressions(c.get("structure") or "")):
                    has = True
                    break
        with_context += 1 if has else 0
    breadth = (with_context / len(pous)) if pous else 0.0
    return token_count, _round4(avg), _round4(breadth)

def _exclusivity_coverage(proj):
    """
    Fraction of rungs (coils) that include both NEGATED and NON-NEGATED contacts for the same base tag.
    """
    rungs_all = 0
    rungs_ok = 0
    for p in _get_program_pous(proj):
        if (p.get("bodyType","").upper() not in ("LD","RLL","LADDER")):
            continue
        rungs = _build_rungs_from_ld(p)
        for rg in rungs:
            rungs_all += 1
            seen_pos = set()
            seen_neg = set()
            for v, neg in rg["contacts"]:
                b = _base_tag(v)
                if neg is True:
                    seen_neg.add(b)
                elif neg is False:
                    seen_pos.add(b)
            if seen_pos & seen_neg:
                rungs_ok += 1
    return _round4(rungs_ok / rungs_all) if rungs_all else 0.0

def _redundancy_diversity_ratio(proj):
    """
    Heuristic: rung is 'diverse' if a coil has 2+ upstream branches (multiple distinct immediate inputs)
    whose contact variable sets differ.
    """
    total = 0
    ok = 0
    for p in _get_program_pous(proj):
        if (p.get("bodyType","").upper() not in ("LD","RLL","LADDER")):
            continue
        cmap = _get_components(p)
        # map from localId -> list[refLocalId]
        inputs = {lid: _conn_in_ids(c) for lid, c in cmap.items()}
        rungs = _build_rungs_from_ld(p)
        for rg in rungs:
            total += 1
            coil = rg["coil_id"]
            heads = inputs.get(coil) or []
            if len(heads) < 2:
                continue
            # collect contact tags per head
            tags_per_head = []
            for h in heads:
                # walk upstream from head, gather contact base tags
                tags = set()
                q = deque([h])
                visited = set()
                while q:
                    nid = q.popleft()
                    if nid in visited:
                        continue
                    visited.add(nid)
                    c = cmap.get(nid, {})
                    if (c.get("type") or "").lower() == "contact":
                        name, _neg = _parse_contact_info(c.get("structure") or "")
                        if name:
                            tags.add(_base_tag(name))
                    for up in _conn_in_ids(c):
                        q.append(up)
                tags_per_head.append(tuple(sorted(tags)))
            if len(set(tags_per_head)) > 1:
                ok += 1
    return _round4(ok / total) if total else 0.0

def _coverage_by_category(proj):
    """
    Build same coverage metrics as L5X but from Codesys ladder artifacts.
    We evaluate per rung (coil) using contacts, blocks and expressions.
    """
    var_index = _build_var_index(proj)

    def var_kind(name: str):
        meta = var_index.get(_base_tag(name))
        if not meta:
            return None
        return meta.get("phyOutIn")  # 'input' | 'output' | None

    # tallies
    in_total = in_ok = 0
    out_total = out_ok = 0
    pv_total = pv_ok = 0
    cv_total = cv_ok = 0
    pid_total = pid_ok = 0
    sp_total = sp_ok = 0
    tmr_total = tmr_ok = 0
    scl_total = scl_ok = 0
    ctr_total = ctr_ok = 0
    unknown_total = unknown_ok = 0
    safe_in_total = safe_in_ok = 0
    safe_out_total = safe_out_ok = 0

    def has_comparator(blocks, exprs):
        if any(b.upper() in COMPARATORS for b in blocks):
            return True
        txt = " ".join(exprs).lower()
        return bool(re.search(r"\b(<|>|<=|>=|==|<>|!=)\b", txt))
    def mentions_pv(exprs, contacts):
        txt = " ".join(exprs + [c for c,_ in contacts]).lower()
        return ".pv" in txt or " pv" in f" {txt}"
    def mentions_cv(exprs, contacts):
        txt = " ".join(exprs + [c for c,_ in contacts]).lower()
        return ".cv" in txt or " cv" in f" {txt}" or "_cv" in txt
    def mentions_sp(exprs, contacts):
        txt = " ".join(exprs + [c for c,_ in contacts]).lower()
        return any(k in txt for k in SP_KW)
    def has_timer(blocks, contacts):
        if any(b.upper() in TIMER_BLOCKS for b in blocks):
            return True
        # contact referencing timer.Q is also a tell
        return any("." in (c or "") and c.lower().endswith(".q") for c,_ in contacts)
    def timer_comp(blocks, exprs, contacts):
        # crude: comparator present OR references ET/PRE in expressions
        if has_comparator(blocks, exprs):
            return True
        txt = " ".join(exprs + [c for c,_ in contacts]).lower()
        return ".et" in txt or ".pre" in txt
    def has_counter(blocks):
        return any(b.upper() in COUNTER_BLOCKS for b in blocks)
    def counter_comp(blocks, exprs):
        return has_comparator(blocks, exprs)
    def has_scale(blocks, exprs):
        if any(b.upper() in {"LIMIT","MIN","MAX"} for b in blocks):
            return True
        txt = " ".join(exprs).lower()
        return _contains_any(txt, SCALE_KW) or "((tempsens" in txt  # crude normalization example
    def has_unknown(exprs):
        txt = " ".join(exprs).lower()
        return bool(re.search(r"\b(65535|4294967295|-1|0x?ffff|unknown)\b", txt))

    for p in _get_program_pous(proj):
        if (p.get("bodyType","").upper() not in ("LD","RLL","LADDER")):
            continue
        for rg in _build_rungs_from_ld(p):
            blocks = [b.upper() for b in rg["blocks"]]
            exprs = rg["expressions"]
            contacts = rg["contacts"]
            coil_var = rg["coil_var"] or ""

            comp = has_comparator(blocks, exprs)
            pv = mentions_pv(exprs, contacts)
            cv = mentions_cv(exprs, contacts)
            sp = mentions_sp(exprs, contacts)
            tmr = has_timer(blocks, contacts)
            ctr = has_counter(blocks)
            scl = has_scale(blocks, exprs)
            unk = has_unknown(exprs)

            # Input/output classification using variable index and keywords fallback
            rung_refs = [c for c,_ in contacts] + ([coil_var] if coil_var else [])
            if any((var_kind(x) == "input") for x in rung_refs) or any(_contains_any(x, INPUT_KW) for x in rung_refs):
                in_total += 1
                if comp:
                    in_ok += 1
                if _contains_any(" ".join(rung_refs), SAFETY_KW):
                    safe_in_total += 1
                    safe_in_ok += 1
            if any((var_kind(x) == "output") for x in rung_refs) or (coil_var and var_kind(coil_var) == "output") \
               or _contains_any(coil_var, ACTUATOR_KW):
                out_total += 1
                if comp or _contains_any(" ".join(rung_refs), SAFETY_KW):
                    out_ok += 1
                if _contains_any(" ".join(rung_refs), SAFETY_KW):
                    safe_out_total += 1
                    safe_out_ok += 1

            if pv:
                pv_total += 1
                if comp:
                    pv_ok += 1
            if cv:
                cv_total += 1
                if comp:
                    cv_ok += 1
            if _contains_any(" ".join(exprs + [coil_var] + [c for c,_ in contacts]), PID_KW):
                pid_total += 1
                if comp:
                    pid_ok += 1
            if sp:
                sp_total += 1
                if comp:
                    sp_ok += 1
            if tmr:
                tmr_total += 1
                if timer_comp(blocks, exprs, contacts):
                    tmr_ok += 1
            if scl:
                scl_total += 1
                if comp:
                    scl_ok += 1
            if ctr:
                ctr_total += 1
                if counter_comp(blocks, exprs):
                    ctr_ok += 1
            if unk:
                unknown_total += 1
                unknown_ok += 1

    def frac(ok, tot):
        return _round4(ok / tot) if tot else 0.0

    return {
        "Physical_Input_Reasonability_Coverage": frac(in_ok, in_total),
        "Physical_Output_Reasonability_Coverage": frac(out_ok, out_total),
        "Process_Variable_Reasonability_Coverage": frac(pv_ok, pv_total),
        "Control_Variable_Reasonability_Coverage": frac(cv_ok, cv_total),
        "PID_Term_Reasonability_Coverage": frac(pid_ok, pid_total),
        "Set_Point_Reasonability_Coverage": frac(sp_ok, sp_total),
        "Timer_Reasonability_Coverage": frac(tmr_ok, tmr_total),
        "Scale_Block_Reasonability_Coverage": frac(scl_ok, scl_total),
        "Counter_Reasonability_Coverage": frac(ctr_ok, ctr_total),
        "Unknown_Signals_Detection": frac(unknown_ok, max(unknown_total, 1)),
        "Safe_Input_Coverage": frac(safe_in_ok, safe_in_total),
        "Safe_Output_Coverage": frac(safe_out_ok, safe_out_total),
    }

def _number_of_rungs_codesys(proj):
    """Heuristic: number of coil components across LD/RLL POUs."""
    count = 0
    for p in _get_program_pous(proj):
        if (p.get("bodyType","").upper() not in ("LD","RLL","LADDER")):
            continue
        cmap = _get_components(p)
        count += sum(1 for c in cmap.values() if (c.get("type") or "").lower() == "coil")
    return count

def _config_awareness_breadth(proj):
    """Fraction of POUs that mention configuration terms in vars/docs/expressions."""
    pous = _get_program_pous(proj)
    hits = 0
    for p in pous:
        seen = False
        iface = p.get("interface") or {}
        for v in _collect_all_vars_from_interface(iface):
            if _contains_any(v.get("name") or "", CONFIG_KW) or _contains_any(v.get("documentation") or "", CONFIG_KW):
                seen = True
                break
        if not seen:
            comps = _get_components(p)
            for c in comps.values():
                s = c.get("structure") or ""
                plain = re.sub(r"<.*?>", " ", s)
                if _contains_any(plain, CONFIG_KW):
                    seen = True
                    break
        hits += 1 if seen else 0
    return (hits / len(pous)) if pous else 0.0

# ---------------------- public API ----------------------

def compute_metrics(proj: dict, source_path: str | None = None) -> dict:
    """
    Compute metrics dict following the same schema as L5X metrics.json.
    """
    # File size if available
    fsize = 0
    if source_path and Path(source_path).exists():
        try:
            fsize = Path(source_path).stat().st_size
        except Exception:
            fsize = 0

    num_lines = _count_lines_codesys(proj)
    num_rungs = _number_of_rungs_codesys(proj)
    pous = _get_program_pous(proj)
    num_pous = len(pous)
    program_names = _collect_program_names(proj)
    langs, _total, rll_pct = _collect_languages(proj)
    n_tags_total, n_tags_ctrl, n_tags_prog = _collect_tag_counts(proj)

    psa_cnt, psa_content = _psa_terms(proj)
    terms_in = _terms_catalog(proj)
    token_count, avg_context, breadth = _discoverability(proj)
    exclusivity = _exclusivity_coverage(proj)
    rd_ratio = _redundancy_diversity_ratio(proj)
    cov = _coverage_by_category(proj)

    metrics = {
        "Number_of_Lines:": {"value": num_lines},
        "File_Size:": {"value": fsize},
        "Number_of_Rungs:": {"value": num_rungs},
        "Number_of_POUs:": {"value": num_pous},
        "Program_Names:": {"value": ",".join(program_names)},
        "Number_of_Languages:": {"value": len(langs)},
        "Language_RLL_Percentage:": {"value": _round4(rll_pct)},
        "Number_of_Tags:": {"value": n_tags_total},
        "Number_of_Tags_in_Controller:": {"value": n_tags_ctrl},
        "Number_of_Tags_in_Programs:": {"value": n_tags_prog},
        "PSA_Count:": {"value": psa_cnt},
        "PSA_Content:": {"value": psa_content},
        "List_Of_Terms_In:": {"value": terms_in},
        "Raw_Context_Discoverability:": {"value": token_count},
        "Average_Context_Discoverability:": {"value": avg_context},
        "Discoverability_Breadth:": {"value": breadth},
        "Exclusivity_Coverage:": {"value": exclusivity},
        "Physical_Input_Reasonability_Coverage": {"value": cov["Physical_Input_Reasonability_Coverage"]},
        "Physical_Output_Reasonability_Coverage": {"value": cov["Physical_Output_Reasonability_Coverage"]},
        "Process_Variable_Reasonability_Coverage": {"value": cov["Process_Variable_Reasonability_Coverage"]},
        "Control_Variable_Reasonability_Coverage": {"value": cov["Control_Variable_Reasonability_Coverage"]},
        "PID_Term_Reasonability_Coverage:": {"value": cov["PID_Term_Reasonability_Coverage"]},
        "Set_Point_Reasonability_Coverage:": {"value": cov["Set_Point_Reasonability_Coverage"]},
        "Timer_Reasonability_Coverage:": {"value": cov["Timer_Reasonability_Coverage"]},
        "Scale_Block_Reasonability_Coverage:": {"value": cov["Scale_Block_Reasonability_Coverage"]},
        "Counter_Reasonability_Coverage:": {"value": cov["Counter_Reasonability_Coverage"]},
        "Redundancy_and_Diversity_Ratio:": {"value": rd_ratio},
        "Unknown_Signals_Detection:": {"value": cov["Unknown_Signals_Detection"]},
        "Safe_Input_Coverage:": {"value": cov["Safe_Input_Coverage"]},
        "Safe_Output_Coverage:": {"value": cov["Safe_Output_Coverage"]},
        "Configuration_Awareness_Breadth:": {"value": _round4(_config_awareness_breadth(proj))},
    }
    return metrics

def write_metrics(proj: dict, source_path: str, exports_dir: Path, base_name: str, timestamp: str) -> Path:
    """
    Compute and write metrics JSON alongside your export.
    Returns the output Path.
    """
    metrics = compute_metrics(proj, source_path=source_path)
    out_path = exports_dir / f"{base_name}_metrics_{timestamp}.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(metrics, f, indent=2)
    logger.info("Metrics written to %s", out_path.resolve())
    return out_path

# Optional CLI for ad-hoc usage: give it a parsed Codesys JSON file.
if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser(description="Compute metrics from a parsed Codesys JSON file.")
    ap.add_argument("parsed_json", help="Path to the parsed project JSON (output of your Codesys parser).")
    ap.add_argument("--source", help="Original Codesys XML path (for File_Size)", default=None)
    ap.add_argument("--out", help="Output metrics path (default: alongside parsed_json)", default=None)
    args = ap.parse_args()

    pdata = json.loads(Path(args.parsed_json).read_text(encoding="utf-8"))
    metrics = compute_metrics(pdata, source_path=args.source)
    out = Path(args.out) if args.out else Path(args.parsed_json).with_name(Path(args.parsed_json).stem + "_metrics.json")
    out.write_text(json.dumps(metrics, indent=2), encoding="utf-8")
    print(f"Metrics written to {out.resolve()}")
