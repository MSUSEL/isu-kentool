#!/usr/bin/env python3
"""
owlalyze.py

CLI entry point for OWLalyze: parsing PLC XML configuration files
for later safety metric analysis (CODESYS IEC 61131-3 and Rockwell .l5x).
Ignores namespaces (assumes none), includes error checks and branching support.
"""

# MODIFIED FUNCTION _PARSE INSTRUCTIONS.
# It was throwing an error parsing OP codes when it came across AI_01. It was only parsing letters and then looking for "(", 
# So when it got to _ it faulted. This may or may not cause unintended consequenses, will need to watch
# I am concerned that it might label a variable or such as an OPcode unintentially.
# Glake - 10/2025

import argparse
import logging
import re
import xml.etree.ElementTree as ET
from pathlib import Path
from datetime import datetime
import json
from metrics_l5x import write_metrics
from metrics_codesys import write_metrics as write_codesys_metrics

def parse_codesys_xml(file_path):
    """
    Parse a IEC 61131-3 XML file, stripping namespaces from tags.
    Extracts project metadata and variables from <variable> elements where address starts
    with '%Q' (Outputs), with '%I' (Inputs), and internal variables.
    Builds logic paths via ladder (LD elements) and structured text (ST elements).
    Returns {'project': project_info, 'logic': logic_paths} or None on error.
    """
    try:
        tree = ET.parse(file_path)
    except (ET.ParseError, IOError) as e:
        logging.error(f"Failed to parse IEC 61131-3 XML: {e}")
        return None
    root = tree.getroot()
    # Strip default namespace
    for elem in root.iter():
        if isinstance(elem.tag, str) and '}' in elem.tag:
            elem.tag = elem.tag.split('}', 1)[1]

    project_info = {}
    pous_info = []  # New list to hold all POU details

    # --- Part 1: fileHeader and contentHeader --- 
    fh = root.find('fileHeader')
    if fh is not None:
        project_info['companyName'] = fh.get('companyName')
        project_info['companyURL'] = fh.get('companyURL', '')
        project_info['productName'] = fh.get('productName')
        project_info['productVersion'] = fh.get('productVersion')
        project_info['productRelease'] = fh.get('productRelease', '')
        project_info['creationDateTime'] = fh.get('creationDateTime')
        project_info['contentDescription'] = fh.get('contentDescription', '')
    ch = root.find('contentHeader')
    if ch is not None:
        project_info['name'] = ch.get('name')
        project_info['version'] = ch.get('version', '')
        project_info['modificationDateTime'] = ch.get('modificationDateTime', '')
        project_info['organization'] = ch.get('organization','')
        project_info['author'] = ch.get('author', '')
        project_info['language'] = ch.get('language', '')

    # --- Part 2: instances -> configurations -> configuration -> resource ---
    instances = root.find('instances')
    if instances is not None:
        configurations_parent = instances.find('configurations')
        configurations_list = []

        if configurations_parent is not None:
            for config in configurations_parent.findall('configuration'):
                config_obj = {'name': config.get('name', ''), 'resources': []}

                # Walk resources under this configuration
                for resource in config.findall('resource'):
                    resource_obj = {'name': resource.get('name', ''), 'tasks': []}

                    # --- Part 3: Parse tasks inside resource ---
                    for task in resource.findall('task'):
                        task_obj = {
                            'name': task.get('name', ''),
                            'interval': task.get('interval', ''),
                            'priority': task.get('priority', ''),
                            'taskSettings': None  # will populate if found
                        }

                        # Look inside <addData> for TaskSettings
                        add_data = task.find('addData')
                        if add_data is not None:
                            for data_elem in add_data.findall('data'):
                                if 'tasksettings' in data_elem.get('name', '').lower():
                                    # Found TaskSettings element
                                    task_settings_elem = data_elem.find('TaskSettings')
                                    if task_settings_elem is not None:
                                        task_settings = {
                                            'KindOfTask': task_settings_elem.get('KindOfTask', ''),
                                            'Interval': task_settings_elem.get('Interval', ''),
                                            'IntervalUnit': task_settings_elem.get('IntervalUnit', ''),
                                            'WithinSPSTimeSlicing': task_settings_elem.get('WithinSPSTimeSlicing', ''),
                                            'Watchdog': None
                                        }
                                        # Watchdog element
                                        watchdog_elem = task_settings_elem.find('Watchdog')
                                        if watchdog_elem is not None:
                                            task_settings['Watchdog'] = {
                                                'Enabled': watchdog_elem.get('Enabled', ''),
                                                'TimeUnit': watchdog_elem.get('TimeUnit', ''),
                                                'Sensitivity': watchdog_elem.get('Sensitivity', '')
                                            }
                                        task_obj['taskSettings'] = task_settings

                        resource_obj['tasks'].append(task_obj)

                        # --- Part 4: Parse addData inside resource for POU info ---
                        add_data_resource = resource.find('addData')
                        if add_data_resource is not None:
                            for data_elem in add_data_resource.findall('data'):
                                pou_elem = data_elem.find('pou')
                                if pou_elem is not None:
                                    pou_info = {
                                        'name': pou_elem.get('name', ''),
                                        'pouType': pou_elem.get('pouType', ''),
                                        'interface': {},
                                        'body': None
                                    }

                                    # Parse interface
                                    interface_elem = pou_elem.find('interface')
                                    if interface_elem is not None:
                                        # Known variable collections
                                        var_sections = ['localVars', 'tempVars', 'inputVars', 'outputVars',
                                                        'inOutVars', 'externalVars', 'globalVars', 'accessVars']
                                        for section in var_sections:
                                            section_elem = interface_elem.find(section)
                                            pou_info['interface'][section] = []
                                            if section_elem is not None:
                                                for var_elem in section_elem.findall('variable'):
                                                    var_info = parse_variable(var_elem)
                                                    pou_info['interface'][section].append(var_info)

                                    # Parse body
                                    body_elem = pou_elem.find('body')
                                    if body_elem is not None:
                                        if body_elem.find('LD') is not None:
                                            ld_elem = body_elem.find('LD')
                                            components, ld_lookup = parse_ld_element(ld_elem)
                                            pou_info['bodyType'] = 'LD'
                                            pou_info['ldComponents'] = components
                                            pou_info['ldComponentLookup'] = ld_lookup 
                                            pou_info['sankey_data'] = generate_sankey_data(components)
        
                                        else:
                                            # Other languages like IL, ST, FBD, SFC → just store XML for future
                                            for lang in ['IL', 'ST', 'FBD', 'SFC']:
                                                lang_elem = body_elem.find(lang)
                                                if lang_elem is not None:
                                                    pou_info['bodyType'] = lang
                                                    pou_info['rawBody'] = ET.tostring(lang_elem, encoding='unicode')
                                                    break

                                    pous_info.append(pou_info)

                    config_obj['resources'].append(resource_obj)

                configurations_list.append(config_obj)

            # Store configurations tree in project_info
            project_info['instances'] = {'configurations': configurations_list}
            project_info['pous'] = pous_info

    return project_info

def parse_variable(var_elem):
    """Parse a <variable> element into a structured dict."""
    var_info = {
        'name': var_elem.get('name', ''),
        'address': var_elem.get('address', None),
        'physical': bool(var_elem.get('address', None)),
        'phyOutIn': None,
        'type': None,
        'initialValue': None,
        'documentation': None
    }

    # Parse Physical Output or Input
    if not var_info['address'] == None and var_info['address'].startswith('%Q'):
        var_info['phyOutIn'] = 'output'
    elif not var_info['address'] == None and var_info['address'].startswith('%I'):
        var_info['phyOutIn'] = 'input'
    else:
        var_info['phyOutIn'] = None

    # Parse type
    type_elem = var_elem.find('type')
    if type_elem is not None and len(type_elem):
        type_child = list(type_elem)[0]  # first child
        if type_child.tag == 'derived':
            var_info['type'] = f"derived-{type_child.get('name', '')}"
        elif type_child.tag == 'array':
            # Array: get dimensions and baseType
            dim_elem = type_child.find('dimension')
            base_type_elem = type_child.find('baseType')
            base_type_name = None
            if base_type_elem is not None and len(base_type_elem):
                base_type_name = list(base_type_elem)[0].tag
            var_info['type'] = 'array'
            var_info['arrayInfo'] = {
                'lower': dim_elem.get('lower', '') if dim_elem is not None else '',
                'upper': dim_elem.get('upper', '') if dim_elem is not None else '',
                'baseType': base_type_name
            }
        else:
            var_info['type'] = type_child.tag

    # Parse initialValue
    init_elem = var_elem.find('initialValue')
    if init_elem is not None and len(init_elem):
        init_child = list(init_elem)[0]
        var_info['initialValue'] = {
            'value': init_child.get('value', ''),
            'valueType': init_child.tag
        }

    # Parse documentation
    doc_elem = var_elem.find('documentation')
    if doc_elem is not None:
        xhtml_elem = doc_elem.find('xhtml')
        if xhtml_elem is not None and xhtml_elem.text:
            var_info['documentation'] = xhtml_elem.text.strip()

    return var_info

def parse_ld_element(ld_elem):
    """Parses an LD element into a list of components and a lookup by localId."""
    components = []
    component_lookup = {}

    for elem in ld_elem:
        obj_type = elem.tag
        local_id = elem.get('localId')

        # Base object structure
        comp = {
            'type': obj_type,
            'localId': local_id,
            'connectionsIn': [],
            'connectionsOut': [],
            'structure': ""
        }

        # Remove only line breaks and indentation (not inside tags or values)
        xml_str = ET.tostring(elem, encoding="unicode", method="xml")
        comp['structure'] = compact_xml_string(xml_str)

        # Upstream connections
        for cp_in in elem.findall('connectionPointIn'):
            for conn in cp_in.findall('connection'):
                ref_id = conn.get('refLocalId')
                if ref_id is not None:
                    comp['connectionsIn'].append({'refLocalId': ref_id})

        # Downstream connections
        for cp_out in elem.findall('connectionPointOut'):
            for conn in cp_out.findall('connection'):
                ref_id = conn.get('refLocalId')
                comp['connectionsOut'].append({'refLocalId': ref_id})

        # --- FUTURE WORK: Type-specific parsing branches ---
        '''if obj_type == 'comment':
            content_elem = elem.find('content')
            if content_elem is not None:
                xhtml = content_elem.find('{http://www.w3.org/1999/xhtml}xhtml')
                comp['comment'] = xhtml.text.strip() if xhtml is not None and xhtml.text else ''

        elif obj_type == 'vendorElement':
            alt_text = elem.find('alternativeText')
            if alt_text is not None:
                xhtml = alt_text.find('{http://www.w3.org/1999/xhtml}xhtml')
                comp['vendorText'] = xhtml.text.strip() if xhtml is not None and xhtml.text else ''
            # Additional vendor-specific types
            for data in elem.findall('addData/data'):
                if 'fbdelementtype' in data.get('name', '').lower():
                    elt_type = data.find('ElementType')
                    if elt_type is not None and elt_type.text:
                        comp['vendorElementType'] = elt_type.text.strip()
                if 'ldparallelbranch' in data.get('name', '').lower():
                    comp['parallelBranch'] = ET.tostring(data.find('ParallelBranch'), encoding='unicode')

        elif obj_type == 'inVariable':
            expr = elem.findtext('expression')
            if expr:
                comp['expression'] = expr.strip()

        elif obj_type == 'block':
            comp['typeName'] = elem.get('typeName', '')
            comp['inputs'] = []
            comp['outputs'] = []
            for in_var in elem.findall('inputVariables/variable'):
                param = in_var.get('formalParameter')
                refs = [conn.get('refLocalId') for conn in in_var.findall('connectionPointIn/connection')]
                comp['inputs'].append({'formalParameter': param, 'refLocalIds': refs})
            for out_var in elem.findall('outputVariables/variable'):
                param = out_var.get('formalParameter')
                expr = out_var.findtext('connectionPointOut/expression')
                comp['outputs'].append({'formalParameter': param, 'expression': expr.strip() if expr else ''})

        elif obj_type == 'contact':
            comp['variable'] = elem.findtext('variable')
            comp['negated'] = elem.get('negated', 'false') == 'true'

        elif obj_type == 'coil':
            comp['variable'] = elem.findtext('variable')
            comp['negated'] = elem.get('negated', 'false') == 'true'

        elif obj_type == 'leftPowerRail' or obj_type == 'rightPowerRail':
            # Usually just positional & connectionPoint presence
            pass'''

        # Store in components list
        components.append(comp)
        if local_id:
            component_lookup[local_id] = comp

    return components, component_lookup

def build_reverse_ld_paths(ld_components):
    """
    Builds reverse logic paths from outputs (coils, blocks before rightPowerRail) to their input sources.
    Returns a dict of output localId -> list of input localIds that influence it.
    """
    id_to_comp = {comp.get('localId'): comp for comp in ld_components if comp.get('localId')}
    graph = {}  # output_localId: set(input_localIds)

    # Step 1: Identify rightPowerRail's localId
    right_power_id = None
    for comp in ld_components:
        if comp['type'] == 'rightPowerRail':
            right_power_id = comp.get('localId')
            break

    # Step 2: Identify terminal components (connected to rightPowerRail or with no outputs)
    terminal_ids = set()
    for comp in ld_components:
        local_id = comp.get('localId')
        if not local_id or comp['type'] == 'rightPowerRail':
            continue
        # Exclude rightPowerRail, but include anything directly connected to it
        for conn in comp.get('connectionsOut', []):
            if conn.get('refLocalId') == right_power_id:
                terminal_ids.add(local_id)
        if not comp.get('connectionsOut'):  # dead-ends
            terminal_ids.add(local_id)

    # Step 3: Recursive walk upstream from each terminal
    def walk_upstream(start_id, visited=None):
        if visited is None:
            visited = set()
        if start_id in visited:
            return set()
        visited.add(start_id)

        comp = id_to_comp.get(start_id)
        if not comp:
            return set()

        upstream_ids = set()
        for in_conn in comp.get('connectionsIn', []):
            src_id = in_conn.get('refLocalId')
            if src_id and src_id != '0':  # don't include leftPowerRail
                upstream_ids.add(src_id)
                upstream_ids.update(walk_upstream(src_id, visited))
        return upstream_ids

    # Step 4: Build graph
    for output_id in terminal_ids:
        inputs = walk_upstream(output_id)
        graph[output_id] = sorted(inputs)

    return graph

# FUTURE FUNCTION TO PAIR WITH A SUNKEY VISUALIZATION OF LOGIC FLOW IN A PROGRAM
def generate_sankey_data(ld_components):
    """
    Generates node/link data structure for D3 Sankey diagram from LD components.
    Returns:
      sankey_dict = {
        'nodes': [{'name': '...'}, ...],
        'links': [{'source': i, 'target': j, 'value': 1}, ...]
      }
    """
    # Step 1: Build lookup for components by localId
    id_to_comp = {comp.get('localId'): comp for comp in ld_components if comp.get('localId')}
    
    # Step 2: Generate unique node names and index them
    node_names = []
    id_to_node_index = {}  # maps localId to node index in node_names
    for comp in ld_components:
        local_id = comp.get('localId')
        if not local_id:
            continue
        comp_type = comp.get('type')
        label = f"{comp_type.upper()} ({local_id})"

        # If it's a variable-based component, add context
        if 'variable' in comp:
            label = f"{comp['variable']} [{comp_type.upper()}] ({local_id})"
        elif comp_type == 'block':
            label = f"{comp.get('typeName', 'BLOCK')} [{comp_type.upper()}] ({local_id})"

        id_to_node_index[local_id] = len(node_names)
        node_names.append({'name': label})

    # Step 3: Build links using connectionsIn (reverse edges)
    links = []
    for target_id, target_comp in id_to_comp.items():
        target_idx = id_to_node_index.get(target_id)
        if target_idx is None:
            continue

        for conn_in in target_comp.get('connectionsIn', []):
            source_id = conn_in.get('refLocalId')
            if source_id and source_id != '0':  # skip leftPowerRail
                source_idx = id_to_node_index.get(source_id)
                if source_idx is not None:
                    links.append({'source': source_idx, 'target': target_idx, 'value': 1})

    sankey_data = {
        'nodes': node_names,
        'links': links
    }

    return sankey_data

def compact_xml_string(xml_str):
    xml_str = xml_str.strip()
    xml_str = xml_str.replace('\n', '').replace('\r', '').replace('\t', '')
    xml_str = re.sub(r'>\s+<', '><', xml_str)  # remove spaces between tags
    return xml_str


# ============== L5X Section =======================
# ===================== General helpers =====================

def _to_native(value: str):
    if value is None:
        return None
    v = value.strip()
    low = v.lower()
    if low in ("true", "false"):
        return low == "true"
    if v.startswith("16#"):  # Keep Logix hex-like literals as strings
        return v
    if v.isdigit():
        try:
            return int(v)
        except ValueError:
            pass
    return v

def _attrs(elem, drop_keys=None):
    drop_keys = drop_keys or set()
    out = {}
    for k, v in elem.attrib.items():
        if k in drop_keys:
            continue
        out[k] = _to_native(v)
    return out

def _collect_text_recursive(node):
    if node is None:
        return None
    parts = []
    def walk(n):
        if n.text:
            parts.append(n.text)
        for c in n:
            walk(c)
        if n.tail:
            parts.append(n.tail)
    walk(node)
    s = "".join(parts).strip()
    return s if s else None

def _serialize_element(elem):
    return ET.tostring(elem, encoding="unicode") if elem is not None else None

def _seek_next_token_start(src: str, i: int) -> int:
    """
    Advance i to the next plausible opcode start (A-Z){3} or structural token ([ or ,).
    Stops at end of string. Safe to call anywhere.
    """
    n = len(src)
    while i < n:
        ch = src[i]
        if ('A' <= ch <= 'Z') or ch in '[,':
            break
        # skip anything else: whitespace, ']', ';', etc.
        i += 1
    return i

def _localname(tag: str) -> str:
    """Return local element name sans namespace, e.g. '{ns}FBDContent' -> 'FBDContent'."""
    return tag.split('}', 1)[-1] if '}' in tag else tag

def _child_by_localname(el: ET.Element, name_ci: str) -> ET.Element | None:
    """Find direct child whose localname matches name_ci (case-insensitive)."""
    target = name_ci.lower()
    for c in el:
        if _localname(c.tag).lower() == target:
            return c
    return None

def _find_first_deep_by_localname(el: ET.Element, name_ci: str) -> ET.Element | None:
    """Find first descendant whose localname matches name_ci (case-insensitive)."""
    target = name_ci.lower()
    for c in el.iter():
        if c is el:
            continue
        if _localname(c.tag).lower() == target:
            return c
    return None

# ===================== Rung Text → Linked Graph =====================

_CDATA_OPEN = "<![CDATA["
_CDATA_CLOSE = "]]>"

def strip_cdata(s: str) -> str:
    if not s:
        return s
    s = s.strip()
    if s.startswith(_CDATA_OPEN) and s.endswith(_CDATA_CLOSE):
        return s[len(_CDATA_OPEN):-len(_CDATA_CLOSE)].strip()
    return s

def _skip_ws(src: str, i: int) -> int:
    n = len(src)
    while i < n and src[i].isspace():
        i += 1
    return i

def _find_matching(src: str, i: int, open_ch='[', close_ch=']') -> int:
    n = len(src)
    if i >= n or src[i] != open_ch:
        raise ValueError(f"Expected '{open_ch}' at pos {i}")
    depth = 1
    j = i + 1
    while j < n and depth > 0:
        ch = src[j]
        if ch == open_ch:
            depth += 1
        elif ch == close_ch:
            depth -= 1
            if depth == 0:
                return j
        j += 1
    raise ValueError(f"No matching '{close_ch}' for '{open_ch}' at pos {i}")

def _parse_instruction(src: str, i: int):
    """
    Parse OP(args) starting at src[i].
    Returns ({"op": OP, "args":[...]}, new_index).
    """
    n = len(src)
    j = i
    # MODIFIED THIS INSTRUCTION TO LOOK FOR _ or NUMBERS. THIS MIGHT CAUSE FUTURE PROBLEMS WITH VARIABLES VS OPCODES - GLAKE 10/2025
    while j < n and ('A' <= src[j] <= 'Z' or src[j] == '_' or '0' <= src[j] <= '9'):
        j += 1
    if j == i:
        raise ValueError(f"Expected opcode at pos {i}")
    op = src[i:j]
    if j >= n or src[j] != '(':
        raise ValueError(f"Expected '(' after opcode {op} at pos {j}")
    # parse args to ')'
    j += 1
    start = j
    depth = 1
    while j < n and depth > 0:
        ch = src[j]
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
            if depth == 0:
                break
        j += 1
    if depth != 0:
        raise ValueError(f"Unterminated args for {op}")
    arg_str = src[start:j].strip()
    args = [a.strip() for a in arg_str.split(",") if a.strip()]
    j += 1  # past ')'
    return {"op": op, "args": args}, j

def _parse_series(src: str, start_i: int, end_i: int):
    """
    Parse a series of instructions from src[start_i:end_i].
    - Skips top-level commas, stray brackets/semicolons/whitespace
    - Flattens any unexpected inner [..] defensively
    """
    i = start_i
    series = []
    while i < end_i:
        i = _skip_ws(src, i)
        if i >= end_i:
            break
        ch = src[i]

        if ch == '[':
            j = _find_matching(src, i, '[', ']')
            # Flatten defensively: treat as just another series chunk
            leg_series, _ = _parse_series(src, i+1, j)
            series.extend(leg_series)
            i = j + 1
            continue

        if ch in ',];':
            i += 1
            continue

        i = _seek_next_token_start(src, i)
        if i >= end_i:
            break
        if src[i] in '[,];':
            i += 1
            continue

        instr, i = _parse_instruction(src, i)
        series.append(instr)

    return series, i

def _id_gen(prefix="n"):
    i = 0
    while True:
        yield f"{prefix}{i}"
        i += 1

def _build_series_nodes(instrs, idgen, nodes, attach_to_id=None):
    """
    Build linked list nodes for a series. Returns (head_id, tail_id).
    """
    prev_id = None
    head_id = None
    for ins in instrs:
        nid = next(idgen)
        nodes[nid] = {"id": nid, "op": ins["op"], "args": ins.get("args", []), "next": None, "branch_next": []}
        if prev_id is not None:
            nodes[prev_id]["next"] = nid
        else:
            head_id = nid
        prev_id = nid
    return head_id, (prev_id if prev_id is not None else attach_to_id)

# ---------- helpers for top-level splitting & series parsing ----------

def _split_top_level_commas(src: str) -> list[str]:
    """
    Split 'src' on commas at top-level (not inside () or []).
    Returns list of segments.
    """
    parts = []
    depth_paren = depth_brack = 0
    start = 0
    for i, ch in enumerate(src):
        if ch == '(':
            depth_paren += 1
        elif ch == ')':
            if depth_paren > 0:
                depth_paren -= 1
        elif ch == '[':
            depth_brack += 1
        elif ch == ']':
            if depth_brack > 0:
                depth_brack -= 1
        elif ch == ',' and depth_paren == 0 and depth_brack == 0:
            parts.append(src[start:i])
            start = i + 1
    parts.append(src[start:])
    return [p.strip() for p in parts if p.strip()]

def _parse_top_sequence(src: str):
    """
    Parse a top-level sequence that can contain instructions and inline branch groups.
    Items yielded are:
      - {"type":"instr", "ins": {...}}
      - {"type":"branch", "legs": [ [instr,...], [instr,...], ... ]}
    """
    items = []
    i, n = 0, len(src)
    while i < n:
        i = _skip_ws(src, i)
        if i >= n:
            break
        ch = src[i]

        if ch == '[':
            j = _find_matching(src, i, '[', ']')
            inner = src[i+1:j]
            # split inner into parallel legs by top-level commas
            leg_chunks = _split_top_level_commas(inner) or [inner]
            legs = []
            for chunk in leg_chunks:
                leg_series, _ = _parse_series(chunk, 0, len(chunk))
                if leg_series:
                    legs.append(leg_series)
            if legs:
                items.append({"type": "branch", "legs": legs})
            i = j + 1
            # tolerate an optional comma right after a branch group
            i = _skip_ws(src, i)
            if i < n and src[i] == ',':
                i += 1
            continue

        if ch in ',];':
            i += 1
            continue

        i = _seek_next_token_start(src, i)
        if i >= n or src[i] in '[,];':
            i += 1
            continue

        ins, i = _parse_instruction(src, i)
        items.append({"type": "instr", "ins": ins})

    return items


# ---------- linked-graph builder (replaces _parse_rung_text_to_graph) ----------

def _parse_rung_text_to_graph(s: str):
    """
    Build a linked graph for rung text that may have inline branches or an outer bracket.
    - Final top-level instruction is the output.
    - Inner [ ... ] blocks form parallel legs.
    """
    text = strip_cdata(s or "")
    if not text:
        return None

    tmp = text.strip()
    # Unwrap a single outer [...] if it spans the whole text (optionally followed by ;)
    items_src = tmp
    if tmp.startswith('['):
        try:
            j = _find_matching(tmp, 0, '[', ']')
            tail = tmp[j+1:].strip()
            if j == len(tmp) - 1 or tail in ("", ";"):
                items_src = tmp[1:j].strip()
        except Exception:
            items_src = tmp  # fall back

    if items_src.endswith(';'):
        items_src = items_src[:-1].rstrip()

    items = _parse_top_sequence(items_src)
    if not items:
        return {"parse_error": "No instructions found"}

    idgen = _id_gen()
    nodes = {}
    entry_id = None
    tails = []           # open tails to connect the next item to
    last_node_id = None  # last instruction seen (becomes output)

    def new_node(op, args):
        nid = next(idgen)
        nodes[nid] = {"id": nid, "op": op, "args": args or [], "next": None, "branch_next": []}
        return nid

    for it in items:
        if it["type"] == "instr":
            ins = it["ins"]
            nid = new_node(ins["op"], ins.get("args"))
            for t in tails:
                nodes[t]["next"] = nid
            if entry_id is None:
                entry_id = nid
            tails = [nid]
            last_node_id = nid

        elif it["type"] == "branch":
            legs = it["legs"]
            if not legs:
                continue
            # ensure a single splitter
            if len(tails) != 1:
                split_id = new_node("SPLIT", [])
                for t in tails:
                    nodes[t]["next"] = split_id
                if entry_id is None:
                    entry_id = split_id
                tails = [split_id]
            splitter_id = tails[0]

            branch_heads = []
            branch_tails = []
            for leg in legs:
                head, tail = _build_series_nodes(leg, idgen, nodes)
                if head is None:
                    continue
                branch_heads.append(head)
                branch_tails.append(tail)
            nodes[splitter_id]["branch_next"].extend(branch_heads)
            # Defer reconnection: the *next* instruction will connect all branch tails
            tails = branch_tails

    output_id = last_node_id
    if output_id is None:
        return {"parse_error": "No output instruction found"}

    return {"nodes": nodes, "entry": entry_id or output_id, "output": output_id}

# ===================== Modules helpers =====================

def _collect_module_tags(struct_el):
    struct_dt = struct_el.attrib.get("DataType")
    tags = []
    def walk(node, prefix_parts):
        for dvm in node.findall("DataValueMember"):
            tag_name = ".".join(prefix_parts + [dvm.attrib.get("Name", "")]).strip(".")
            tags.append({
                "structure_datatype": struct_dt,
                "tag": tag_name,
                "datatype": dvm.attrib.get("DataType"),
            })
        for sm in node.findall("StructureMember"):
            sm_name = sm.attrib.get("Name", "")
            walk(sm, prefix_parts + [sm_name])
    walk(struct_el, [])
    return tags

# ===================== Tag helpers (global & program tags) =====================

def _collect_tag_structures(tag_el):
    structures = []
    for s in tag_el.findall(".//Structure"):
        struct_dt = s.attrib.get("DataType")
        members = []
        for dvm in s.findall("DataValueMember"):
            members.append({"name": dvm.attrib.get("Name"), "datatype": dvm.attrib.get("DataType")})
        def walk(sm_node, prefix_parts):
            for dvm in sm_node.findall("DataValueMember"):
                full_name = ".".join(prefix_parts + [dvm.attrib.get("Name", "")]).strip(".")
                members.append({"name": full_name, "datatype": dvm.attrib.get("DataType")})
            for child_sm in sm_node.findall("StructureMember"):
                walk(child_sm, prefix_parts + [child_sm.attrib.get("Name", "")])
        for sm in s.findall("StructureMember"):
            walk(sm, [sm.attrib.get("Name", "")])
        structures.append({"structure_datatype": struct_dt, "members": members})
    return structures

def _collect_tags_under(container_el):
    tag_dict = {}
    if container_el is None:
        return tag_dict
    for t_el in container_el.findall("Tag"):
        t_attrs = _attrs(t_el)
        name = t_attrs.get("Name")
        if not name:
            logging.debug("Encountered <Tag> without Name; skipping.")
            continue
        desc_el = t_el.find("Description")
        description = _collect_text_recursive(desc_el) if desc_el is not None else None
        structures = _collect_tag_structures(t_el)
        tag_dict[name] = {
            "Name": name,
            "DataType": t_attrs.get("DataType"),
            "Constant": t_attrs.get("Constant"),
            "ExternalAccess": t_attrs.get("ExternalAccess"),
            "Description": description,
            "structures": structures,
        }
    logging.debug("Collected %d tags under container", len(tag_dict))
    return tag_dict

# ===================== Main L5X parser =====================

def _parse_rll_rungs(rll_content_el):
    if rll_content_el is None:
        return []
    rung_elems = rll_content_el.findall("Rung")
    if not rung_elems:
        return []
    max_num = 0
    rung_objs = {}
    for r in rung_elems:
        num = _to_native(r.attrib.get("Number"))
        if not isinstance(num, int):
            logging.debug("Skipping rung with non-integer Number: %s", r.attrib.get("Number"))
            continue
        max_num = max(max_num, num)

        comment = _collect_text_recursive(r.find("Comment"))

        # Deepest <Text> node (handles nested <Text><Text>...)
        texts = r.findall(".//Text")
        rung_text_raw = _collect_text_recursive(texts[-1]) if texts else None
        text_clean = strip_cdata(rung_text_raw) if rung_text_raw else None

        logic_graph = _parse_rung_text_to_graph(text_clean) if text_clean else None

        rung_objs[num] = {
            "comment": comment,
            "text": text_clean,          # keep only one copy
            "logic_graph": logic_graph,  # linked list / parallel fan-out
        }

    rungs = [None] * (max_num + 1)
    for idx, obj in rung_objs.items():
        rungs[idx] = obj
    logging.debug("Parsed %d rungs (max index %d)", len(rung_objs), max_num)
    return rungs

def parse_l5x_project_info(xml_text: str) -> dict:
    logging.info("Starting L5X parse from in-memory text.")
    try:
        root = ET.fromstring(xml_text)
    except ET.ParseError as e:
        logging.error("XML parse error: %s", e)
        return {}

    if root.tag != "RSLogix5000Content":
        logging.error("Unexpected root element: %s", root.tag)
        return {}

    # Project (drop unwanted fields)
    project_info = _attrs(
        root,
        drop_keys={"SchemaRevision", "ContainsContext", "ExportDate", "ExportOptions"},
    )
    logging.debug("Project info keys: %s", list(project_info.keys()))

    # Controller (selected fields)
    controller = {}
    controller_el = root.find("Controller")
    if controller_el is None:
        logging.warning("<Controller> element not found.")
    else:
        c_attrs = _attrs(controller_el)
        controller = {
            "Name": c_attrs.get("Name"),
            "ProcessorType": c_attrs.get("ProcessorType"),
            "MajorRev": c_attrs.get("MajorRev"),
            "MinorRev": c_attrs.get("MinorRev"),
        }
        logging.debug("Controller parsed: %s", controller)

    # Modules
    modules = []
    module_nodes = root.findall(".//Modules/Module")
    logging.debug("Found %d modules.", len(module_nodes))
    for m_el in module_nodes:
        m_attrs = _attrs(m_el)
        parent_mod_port = (m_attrs.get("ParentModPortId") or m_attrs.get("ParentModePortId"))
        module_entry = {
            "Name": m_attrs.get("Name"),
            "CatalogNumber": m_attrs.get("CatalogNumber"),
            "ParentModule": m_attrs.get("ParentModule"),
            "ParentModPortId": parent_mod_port,
            "module_tags": [],
        }
        for struct_el in m_el.findall("Structure"):
            module_entry["module_tags"].extend(_collect_module_tags(struct_el))
        modules.append(module_entry)
    logging.debug("Collected module summaries: %d", len(modules))

    # Global Tags
    global_tags = {}
    if controller_el is not None:
        global_tags = _collect_tags_under(controller_el.find("Tags"))
    logging.info("Global tags collected: %d", len(global_tags))

    # Programs (Tags + Routines)
    programs = []
    for p_el in root.findall(".//Programs/Program"):
        p_attrs = _attrs(p_el)
        prog_name = p_attrs.get("Name")
        program_entry = {
            "Name": prog_name,
            "MainRoutineName": p_attrs.get("MainRoutineName"),
            "Disabled": p_attrs.get("Disabled"),
            "tags": _collect_tags_under(p_el.find("Tags")),
            "routines": [],
        }

        routines_el = p_el.find("Routines")
        routine_count = 0
        if routines_el is not None:
            for r_el in routines_el.findall("Routine"):
                r_attrs = _attrs(r_el)
                rtype = r_attrs.get("Type")
                rname = r_attrs.get("Name")
                routine = {
                    "program": prog_name,
                    "Name": rname,
                    "Type": rtype,
                }

                # --- FBD / ST raw content capture (robust to case/namespace/nesting) ---
                if rtype in ("FBD", "ST"):
                    target_local = f"{rtype}Content"   # e.g., FBDContent, STContent
                    content_el = (_child_by_localname(r_el, target_local)
                                  or _find_first_deep_by_localname(r_el, target_local))
                    if content_el is None:
                        logging.debug("Routine '%s' (%s): %s not found", rname, rtype, target_local)
                        routine["content_type"] = rtype
                        routine["raw_content"] = None
                    else:
                        routine["content_type"] = rtype
                        routine["raw_content"] = _serialize_element(content_el)
                        logging.debug("Routine '%s' (%s): captured %s (%d chars)",
                                     rname, rtype, _localname(content_el.tag),
                                     len(routine["raw_content"] or ""))

                # --- RLL / LD rung parsing (also robust to case/namespace) ---
                elif rtype in ("RLL", "LD"):
                    rll_el = (_child_by_localname(r_el, "RLLContent")
                              or _find_first_deep_by_localname(r_el, "RLLContent"))
                    if rll_el is None:
                        logging.debug("Routine '%s' (%s): RLLContent not found", rname, rtype)
                        routine["rungs"] = []
                    else:
                        routine["rungs"] = _parse_rll_rungs(rll_el)

                else:
                    logging.debug("Routine '%s': unknown Type '%s'", rname, rtype)

                program_entry["routines"].append(routine)
                routine_count += 1

        logging.info("Program '%s': tags=%d, routines=%d", prog_name, len(program_entry["tags"]), routine_count)
        programs.append(program_entry)

    result = {
        "project": project_info,
        "controller": controller,
        "modules": modules,
        "global_tags": global_tags,
        "programs": programs,
        "productName": "Studio5000 L5X",
        "productVersion": project_info.get("SoftwareRevision"),
    }
    logging.info("L5X parse complete: programs=%d, modules=%d, global_tags=%d",
                len(programs), len(modules), len(global_tags))
    return result

# ===================== File wrapper for main() =====================

def parse_l5x_xml(path: str) -> dict:
    """
    Read a .l5x/.xml file and parse into a JSON-ready dict.
    Adds logging at file boundaries.
    """
    p = Path(path)
    if not p.exists():
        logging.error("File not found: %s", path)
        return {}
    try:
        text = p.read_text(encoding="utf-8")
    except Exception as e:
        logging.error("Failed to read %s: %s", path, e)
        return {}

    logging.info("Loaded L5X/XML file: %s (%d bytes)", path, len(text))
    data = parse_l5x_project_info(text)
    if not data:
        logging.error("Parsing produced no data for: %s", path)
        return {}
    return data

def main():
    parser = argparse.ArgumentParser(
        description="OWLalyze: Analyze PLC code for safety metrics."
    )
    parser.add_argument("file", nargs="?", help="Path to the PLC XML file (.xml or .l5x) to parse")
    parser.add_argument("--type", choices=["codesys", "l5x"], help="Type of PLC XML file.")
    parser.add_argument("--debug", action="store_true", help="Enable debug logging")
    parser.add_argument("--output-format", choices=["json", "txt"], default="json",
                        help="Output format for future results")
    args = parser.parse_args()
    
    if not args.file:
        args.file = DEFUALT_TEST_FILE

    level = logging.DEBUG if args.debug else logging.INFO
    logging.basicConfig(level=level, format="%(asctime)s [%(levelname)s] %(message)s")
    logging.debug("Debug mode on")

    fpath = args.file
    ftype = args.type or ('l5x' if fpath.lower().endswith('.l5x') else 'codesys')
    logging.debug(f"Parsing {fpath} as {ftype}")

    proj = parse_codesys_xml(fpath) if ftype == 'codesys' else parse_l5x_xml(fpath)
    if not proj:
        logging.error("Parsing returned no data")
        return

    logging.info(f"Project: {proj.get('productName')} version: {proj.get('productVersion','')}")

    # Always write to ./exports/
    exports_dir = Path("exports")
    exports_dir.mkdir(parents=True, exist_ok=True)

    base_name = Path(fpath).stem
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_path = exports_dir / f"{base_name}_export_{timestamp}.{args.output_format}"

    try:
        with open(output_path, "w", encoding="utf-8") as f:
            if args.output_format == "json":
                json.dump(proj, f, indent=2)
            else:  # txt format
                for key, value in proj.items():
                    f.write(f"{key}: {value}\n")
        logging.info(f"Output written to {output_path.resolve()}")
    except Exception as e:
        logging.error(f"Failed to write output: {e}")

    # Build metrics for L5X and write alongside the export
    if ftype == 'l5x':
        try:
            write_metrics(proj, fpath, exports_dir, base_name, timestamp)
        except Exception as e:
            logging.error(f"Failed to compute/write L5X metrics: {e}")
    # ---- Build metrics.json alongside the export for Codesys ----
    if ftype == 'codesys':
        try:
            write_codesys_metrics(proj, fpath, exports_dir, base_name, timestamp)
        except Exception as e:
            logging.error(f"Failed to compute/write Codesys metrics: {e}")

if __name__ == "__main__":
    main()