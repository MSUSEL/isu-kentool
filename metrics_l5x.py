# metrics_l5x.py
# Build OWLalyze metrics from an L5X-parsed project dict.
import json
import logging
import re
from pathlib import Path

logger = logging.getLogger("owlalyze.metrics")

# ---------------------- helpers ----------------------

def _split_tokens(s: str):
    if not s:
        return []
    return re.findall(r"[A-Za-z0-9_\.]{2,}", s)

def _base_tag(name: str):
    if not name:
        return ""
    return re.split(r"[\.\[]", name, 1)[0]

def _round4(x: float) -> float:
    try:
        return float(f"{x:.4f}")
    except Exception:
        return 0.0

def _walk_rungs(proj):
    """Yield (program_name, routine_name, rung_dict)."""
    for p in proj.get("programs", []):
        pname = p.get("Name")
        for r in p.get("routines", []):
            if r.get("Type") in ("RLL", "LD"):
                for rung in (r.get("rungs") or []):
                    if rung:
                        yield pname, r.get("Name"), rung

def _walk_st_fbd(proj):
    """Yield raw ST/FBD content strings."""
    for p in proj.get("programs", []):
        for r in p.get("routines", []):
            if r.get("Type") in ("ST", "FBD"):
                rc = r.get("raw_content")
                if rc:
                    yield rc

def _iter_all_text(proj):
    """All free text: rung text, comments, ST/FBD raw, tag descriptions."""
    for _, _, rung in _walk_rungs(proj):
        if rung.get("text"):
            yield rung["text"]
        if rung.get("comment"):
            yield rung["comment"]
    for rc in _walk_st_fbd(proj):
        yield rc
    # Tag descriptions
    for desc in (proj.get("global_tags") or {}).values():
        if desc.get("Description"):
            yield desc["Description"]
    for p in proj.get("programs", []):
        for tinfo in (p.get("tags") or {}).values():
            if tinfo.get("Description"):
                yield tinfo["Description"]

def _count_lines(proj):
    """Approx line count across rung text/comments and raw ST/FBD content."""
    count = 0
    for _, _, rung in _walk_rungs(proj):
        for s in (rung.get("text") or "", rung.get("comment") or ""):
            if s.strip():
                count += max(1, s.count("\n") + 1)
    for rc in _walk_st_fbd(proj):
        if rc.strip():
            count += max(1, rc.count("\n") + 1)
    return count

def _collect_program_names(proj):
    return [p.get("Name") for p in proj.get("programs", []) if p.get("Name")]

def _collect_languages(proj):
    langs = set()
    total = 0
    rll_cnt = 0
    for p in proj.get("programs", []):
        for r in p.get("routines", []):
            t = r.get("Type")
            if not t:
                continue
            langs.add(t)
            total += 1
            if t in ("RLL", "LD"):
                rll_cnt += 1
    rll_pct = (rll_cnt / total) if total else 0.0
    return langs, total, rll_pct

def _collect_tags(proj):
    ctrl = proj.get("global_tags") or {}
    prog_total = 0
    for p in proj.get("programs", []):
        prog_total += len(p.get("tags") or {})
    return len(ctrl) + prog_total, len(ctrl), prog_total

def _extract_graph_ops_args(rung):
    """Return (ops:set, args:set) from logic_graph if present."""
    ops, args = set(), set()
    g = rung.get("logic_graph") or {}
    for n in (g.get("nodes") or {}).values():
        op = n.get("op")
        if op:
            ops.add(op.upper())
        for a in (n.get("args") or []):
            if a:
                args.add(a)
    return ops, args

def _contains_any(s: str, keywords):
    ls = (s or "").lower()
    return any(k in ls for k in keywords)

def _args_match_any(args, keywords):
    for a in args:
        if _contains_any(a, keywords):
            return True
    return False

# ---------------------- metric estimators ----------------------

COMPARATORS = {"GRT", "GEQ", "LES", "LEQ", "EQU", "NEQ", "LIM"}
TIMERS = {"TON", "TOF", "RTO"}
COUNTERS = {"CTU", "CTD", "CTUD"}

ACTUATOR_KW = ["pump", "motor", "valve", "heater", "fan", "conveyor", "actuator"]
INPUT_KW = ["ai", "input", "sensor", "switch", "pb", "estop", "e-stop", "limit", "ls", "pv", "di", "state"]
SAFETY_KW = ["estop", "e-stop", "trip", "safe", "safety", "esd", "interlock", "guard", "fault", "alarm"]
CONFIG_KW = ["cfg", "config", "parameter", "param", "mode", "recipe", "setup", "enable"]
PID_KW = ["pid", "pide", "kp", "ki", "kd"]
SP_KW = ["setpoint", ".sp", "_sp"]
SCALE_KW = ["scp", "scale", "scaled", "scaling", "scl"]
ALARM_KW = ["alarm", "alm"]
INTERLOCK_KW = ["interlock", "trip", "esd", "estop", "e-stop", "permissive"]
PSA_KW = ["hazop", "lopa", "sil", "sif", "pha", "srs"]

DOMAIN_TERMS = ["pump","pid","motor","valve","heater","tank","level","pressure",
                "flow","temperature","alarm","scale","counter","timer","sensor",
                "actuator","conveyor","mixer"]

def _number_of_rungs(proj):
    return sum(1 for _ in _walk_rungs(proj))

def _exclusivity_coverage(proj):
    """Rungs with both XIC and XIO for same base tag / total rungs."""
    total = 0
    ok = 0
    for _p, _r, rung in _walk_rungs(proj):
        total += 1
        seen_xic, seen_xio = set(), set()
        for n in (rung.get("logic_graph") or {}).get("nodes", {}).values():
            op = (n.get("op") or "").upper()
            for a in (n.get("args") or []):
                b = _base_tag(a)
                if op == "XIC":
                    seen_xic.add(b)
                elif op == "XIO":
                    seen_xio.add(b)
        if seen_xic & seen_xio:
            ok += 1
    return _round4(ok / total) if total else 0.0

def _coverage_by_category(proj):
    """Heuristic coverage metrics, bounded [0,1]."""
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

    for _p, _r, rung in _walk_rungs(proj):
        ops, args = _extract_graph_ops_args(rung)
        text = (rung.get("text") or "").lower()

        has_cmp = any(o in COMPARATORS for o in ops) or bool(re.search(r"\b(LIM|GEQ|GRT|LEQ|LES|EQU|NEQ)\b", text))
        references_pv = (" .pv" in f" {text}") or any(".pv" in (a or "").lower() for a in args)
        references_cv = any(tok in text for tok in [" cv", ".cv", "_cv"]) or _args_match_any(args, ["cv"])
        references_sp = any(k in text for k in SP_KW) or _args_match_any(args, SP_KW)

        has_tmr = any(o in TIMERS for o in ops) or bool(re.search(r"\b(TON|TOF|RTO)\b", text))
        has_tmr_compare = bool(re.search(r"\b(ACC|PRE)\b", text)) or has_cmp

        has_ctr = any(o in COUNTERS for o in ops) or bool(re.search(r"\b(CTU|CTD|CTUD)\b", text))
        has_ctr_compare = has_cmp or bool(re.search(r"\b(ACC|PRE)\b", text))

        has_scale = _contains_any(text, SCALE_KW) or _args_match_any(args, SCALE_KW)

        references_input = _args_match_any(args, INPUT_KW) or _contains_any(text, INPUT_KW)
        references_actuator = _args_match_any(args, ACTUATOR_KW) or _contains_any(text, ACTUATOR_KW)

        mentions_safety = _contains_any(text, SAFETY_KW) or _args_match_any(args, SAFETY_KW)

        has_unknown_sentinel = bool(re.search(r"\b(65535|4294967295|-1|0x?ffff)\b", text, re.I)) or "unknown" in text

        if references_input:
            in_total += 1
            if has_cmp:
                in_ok += 1

        if references_actuator:
            out_total += 1
            if has_cmp or mentions_safety:
                out_ok += 1

        if references_pv:
            pv_total += 1
            if has_cmp:
                pv_ok += 1
        if references_cv:
            cv_total += 1
            if has_cmp:
                cv_ok += 1

        if _contains_any(text, PID_KW) or _args_match_any(args, PID_KW):
            pid_total += 1
            if has_cmp:
                pid_ok += 1

        if references_sp:
            sp_total += 1
            if has_cmp:
                sp_ok += 1

        if has_tmr:
            tmr_total += 1
            if has_tmr_compare:
                tmr_ok += 1

        if has_scale:
            scl_total += 1
            if has_cmp:
                scl_ok += 1

        if has_ctr:
            ctr_total += 1
            if has_ctr_compare:
                ctr_ok += 1

        if has_unknown_sentinel:
            unknown_total += 1
            unknown_ok += 1

        if references_input:
            safe_in_total += 1
            if mentions_safety:
                safe_in_ok += 1
        if references_actuator:
            safe_out_total += 1
            if mentions_safety:
                safe_out_ok += 1

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

def _redundancy_diversity_ratio(proj):
    """Rungs with parallel branches having distinct tags / total rungs."""
    total = 0
    ok = 0
    for _p, _r, rung in _walk_rungs(proj):
        total += 1
        g = rung.get("logic_graph") or {}
        nodes = g.get("nodes") or {}
        if not nodes:
            continue
        splitters = [n for n in nodes.values() if n.get("branch_next")]
        if not splitters:
            continue
        diverse = False
        for sp in splitters:
            heads = sp.get("branch_next") or []
            tags_per_leg = []
            for hid in heads:
                leg_tags = set()
                cur = nodes.get(hid)
                visited = set()
                while cur and cur.get("id") not in visited:
                    visited.add(cur["id"])
                    for a in (cur.get("args") or []):
                        leg_tags.add(_base_tag(a))
                    cur = nodes.get(cur.get("next"))
                tags_per_leg.append(leg_tags)
            if len(tags_per_leg) >= 2:
                sigs = {tuple(sorted(t)) for t in tags_per_leg}
                if len(sigs) > 1:
                    diverse = True
                    break
        if diverse:
            ok += 1
    return _round4(ok / total) if total else 0.0

def _psa_signals(proj):
    """Find PSA/Alarm/Interlock-like signal names; returns (count, content_str)."""
    found_psa, found_alarm, found_inter = set(), set(), set()

    def add_if_kw(name):
        if not name:
            return
        ln = name.lower()
        if any(k in ln for k in PSA_KW):
            found_psa.add(name)
        if any(k in ln for k in ALARM_KW):
            found_alarm.add(name)
        if any(k in ln for k in INTERLOCK_KW):
            found_inter.add(name)

    for tname in (proj.get("global_tags") or {}):
        add_if_kw(tname)
    for p in proj.get("programs", []):
        for tname in (p.get("tags") or {}):
            add_if_kw(tname)

    for _, _, rung in _walk_rungs(proj):
        for tok in _split_tokens(rung.get("text") or ""):
            add_if_kw(tok)
        for tok in _split_tokens(rung.get("comment") or ""):
            add_if_kw(tok)

    groups = []
    if found_psa:
        groups.append(",".join(sorted(found_psa)))
    if found_alarm:
        groups.append(",".join(sorted(found_alarm)))
    if found_inter:
        groups.append(",".join(sorted(found_inter)))
    content = "|".join(groups)
    total = len(found_psa | found_alarm | found_inter)
    return total, content

def _terms_catalog(proj):
    terms = set()
    hay = []
    hay += _collect_program_names(proj)
    hay += list((proj.get("global_tags") or {}).keys())
    for p in proj.get("programs", []):
        hay += list((p.get("tags") or {}).keys())
    for s in _iter_all_text(proj):
        hay.append(s)
    for s in hay:
        ls = (s or "").lower()
        for term in DOMAIN_TERMS:
            if term in ls:
                terms.add(term)
    return ",".join(sorted(terms))

def _config_awareness_breadth(proj):
    total = len(proj.get("programs", [])) or 1
    hits = 0
    for p in proj.get("programs", []):
        seen = False
        if any(_contains_any(k, CONFIG_KW) for k in (p.get("tags") or {}).keys()):
            seen = True
        if not seen:
            for _pn, _rn, rung in _walk_rungs({"programs":[p]}):
                if _contains_any(rung.get("text") or "", CONFIG_KW) or _contains_any(rung.get("comment") or "", CONFIG_KW):
                    seen = True
                    break
        if not seen:
            for r in p.get("routines", []):
                if r.get("Type") in ("ST", "FBD") and _contains_any(r.get("raw_content") or "", CONFIG_KW):
                    seen = True
                    break
        hits += 1 if seen else 0
    return (hits / total) if total else 0.0

# ---------------------- public API ----------------------

def compute_metrics(proj: dict, source_path: str | None = None) -> dict:
    """
    Compute metrics dict (keys shaped like your metrics.json example).
    `proj` is the dict returned by your L5X parser.
    `source_path` is optional and only used to include file size.
    """
    # File size if available
    fsize = 0
    if source_path and Path(source_path).exists():
        try:
            fsize = Path(source_path).stat().st_size
        except Exception:
            fsize = 0

    num_lines = _count_lines(proj)
    num_rungs = _number_of_rungs(proj)
    num_pous = len(proj.get("programs", []))
    program_names = _collect_program_names(proj)
    langs, _total_routines, rll_pct = _collect_languages(proj)
    n_tags_total, n_tags_ctrl, n_tags_prog = _collect_tags(proj)

    psa_cnt, psa_content = _psa_signals(proj)
    terms_in = _terms_catalog(proj)

    # Context discoverability
    token_count = 0
    for s in _iter_all_text(proj):
        token_count += len(re.findall(r"[A-Za-z]{3,}", s or ""))
    token_count += sum(len(re.findall(r"[A-Za-z]{3,}", (n or ""))) for n in program_names)
    token_count += sum(len(re.findall(r"[A-Za-z]{3,}", k or "")) for k in (proj.get("global_tags") or {}).keys())
    for p in proj.get("programs", []):
        token_count += sum(len(re.findall(r"[A-Za-z]{3,}", k or "")) for k in (p.get("tags") or {}).keys())

    avg_context = (token_count / num_lines) if num_lines else 0.0
    # Breadth: programs with any comments/descriptions/typed content
    programs_with_context = 0
    for p in proj.get("programs", []):
        has = False
        if any((t.get("Description") or "").strip() for t in (p.get("tags") or {}).values()):
            has = True
        if not has:
            for _pn, _rn, rung in _walk_rungs({"programs":[p]}):
                if (rung.get("comment") or "").strip():
                    has = True
                    break
        if not has:
            for r in p.get("routines", []):
                if r.get("Type") in ("ST", "FBD") and (r.get("raw_content") or "").strip():
                    has = True
                    break
        programs_with_context += 1 if has else 0
    breadth = (programs_with_context / num_pous) if num_pous else 0.0

    exclusivity = _exclusivity_coverage(proj)
    rd_ratio = _redundancy_diversity_ratio(proj)
    cov = _coverage_by_category(proj)

    # Build metrics using your exact key shapes (some have trailing colons)
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
        "Average_Context_Discoverability:": {"value": _round4(avg_context)},
        "Discoverability_Breadth:": {"value": _round4(breadth)},
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

# Optional: allow running this module directly if someone passes a parsed JSON.
if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser(description="Compute metrics from a parsed L5X JSON file.")
    ap.add_argument("parsed_json", help="Path to the parsed project JSON (output of your parser).")
    ap.add_argument("--source", help="Original .l5x path (for File_Size)", default=None)
    ap.add_argument("--out", help="Output metrics path (default: alongside parsed_json)", default=None)
    args = ap.parse_args()

    pdata = json.loads(Path(args.parsed_json).read_text(encoding="utf-8"))
    metrics = compute_metrics(pdata, source_path=args.source)
    out = Path(args.out) if args.out else Path(args.parsed_json).with_name(Path(args.parsed_json).stem + "_metrics.json")
    out.write_text(json.dumps(metrics, indent=2), encoding="utf-8")
    print(f"Metrics written to {out.resolve()}")
