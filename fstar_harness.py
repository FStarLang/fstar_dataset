#!/usr/bin/env python3
from typing_extensions import TypedDict, Any, Optional, NotRequired
import subprocess
import json
import sys

class Dependency(TypedDict):
  source_file: str
  checked_file: str
  dependencies: list[str]
  depinfo: bool

class OpenOrAbbrev(TypedDict):
  open: NotRequired[str]
  abbrev: NotRequired[bool]
  key: NotRequired[str]
  value: NotRequired[str]

class Vconfig(TypedDict):
  initial_fuel: int
  max_fuel: int
  initial_ifuel: int
  max_ifuel: int
  detail_errors: bool
  detail_hint_replay: bool
  no_smt: bool
  quake_lo: int
  quake_hi: int
  quake_keep: bool
  retry: bool
  smtencoding_elim_box: bool
  smtencoding_nl_arith_repr: str
  smtencoding_l_arith_repr: str
  smtencoding_valid_intro: bool
  smtencoding_valid_elim: bool
  tcnorm: bool
  no_plugins: bool
  no_tactics: bool
  z3cliopt: list[str]
  z3smtopt: list[Any]
  z3refresh: bool
  z3rlimit: int
  z3rlimit_factor: int
  z3seed: int
  z3version: str
  trivial_pre_for_unannotated_effectful_fns: bool
  reuse_hint_for: Optional[Any]

class Definition(TypedDict):
  file_name: str
  start_line: int
  start_col: int
  end_line: int
  end_col: int
  definition: str
  effect: str
  effect_flags: list[str]
  mutual_with: list[Any]
  name: str
  premises: list[str]
  proof_features: list[Any]
  type: str
  source_type: str
  source_definition: str
  prompt: str
  expected_response: str
  opens_and_abbrevs: list[OpenOrAbbrev]
  vconfig: Optional[Vconfig]

class InsightFile(TypedDict):
  defs: list[Definition]
  dependencies: list[Dependency]

# Note: Can we add an option to F* to only load a prefix of a given checked file?
# we want to prevent a candidate proof from relying on out-of-scope parts of an F* checked file
# notably the part including or following the definition/proof we're trying to synthesize
def generate_harness_for_lemma(out_dir, harness_name, extension, scaffolding, needs_interface):
    # Write scaffoling to a file names Harness.module_name.fst
    file_name = f'{out_dir}/{harness_name}.{extension}'
    with open(file_name, "w") as f:
        f.write(scaffolding)
    if needs_interface and extension == "fst":
        module_decl = "module " + harness_name + "\n"
        with open(file_name + "i", "w") as f:
            f.write(module_decl)
    return file_name

# Launch an F* process in interactive mode
def launch_fstar(out_dir, options, harness_name, extension, scaffolding, needs_interface):
    file_name = generate_harness_for_lemma(out_dir, harness_name, extension, scaffolding, needs_interface)
    # Launch F* in interactive mode
    # add --include x for each x in includes
    fstar_args = ["fstar.exe", "--ide", file_name, "--report_assumes", "warn"] + options
    print(f"Launching F* with args: {fstar_args}")
    fstar_process = subprocess.Popen(fstar_args, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
    # check if the process launched without errors
    if fstar_process.poll() is not None:
        print("F* process terminated")
        return None
    return fstar_process


# A function to validate the response from F* interactive mode
def validate_fstar_response(json_objects):
    # parse the each line of the response into a JSON object
    # if the line is not valid JSON, print an error message and exit
    # store the JSON objects in a list
    # check that all the JSON objects have status success
    # if not, print an error message and exit
    for resp in json_objects:
        if resp["kind"] == "message":
            continue
        if resp["kind"] == "protocol-info":
            continue
        if resp["kind"] == "response":
            if resp["status"] != "success":
                print(f"F* reports error: {resp}")
                return (False, resp)
            else:
                continue
        print(f"Error: {resp}")
        return (False, resp)
    return (True, [])


# read the response from stdout
# until we get a line with kind=message and args.kind=full-buffer-finished
def read_full_buffer_response(fstar_process):
    response = ""
    json_objects = []
    while True:
        if fstar_process.poll() is not None:
            print("F* process terminated while reading output")
            # print the full contents of stderr
            for line in fstar_process.stderr.readlines():
                print(f"Error: {line}")
            break
        line = fstar_process.stdout.readline()
        # print a line to stderr for debugging
        # print("Line from F*: <" + line +">", file=sys.stderr)
        if line == "":
            continue
        response = response + line
        resp = json.loads(line)
        json_objects.append(resp)
        if resp["kind"] == "message" and resp["level"] == "progress" and resp["contents"] is not None:
            if resp["contents"]["stage"] == "full-buffer-finished":
                break
    # print ("Response from F*: " + response)
    return json_objects

def check_solution(fstar_process, solution: str):
    check_wf = {"query-id":"2", "query": "full-buffer", "args":{"kind": "full", "with-symbols":False, "code": solution, "line":1, "column":0}}
    #print(f'Asking F* to check solution: {request}')
    fstar_process.stdin.write(json.dumps(check_wf))
    fstar_process.stdin.write("\n")
    fstar_process.stdin.flush()
    # Read the response from stdout
    response_objects = read_full_buffer_response(fstar_process)
    # Validate the response
    return validate_fstar_response(response_objects)

# Read the json file
def read_json_file(filename):
    # open the file and read its contents
    with open(filename) as f:
        data = json.load(f)
    return data

def build_file_scaffolding(deps):
    module_name, extension = deps["source_file"].rsplit(".", 1)
    harness_name = f'Harness_{module_name.replace(".", "_")}'
    if extension == "fsti": harness_name += '_i'
    extension = "fst"
    needs_interface = False
    scaffolding = "module " + harness_name + "\n"
    if len(deps["dependencies"]) > 0 and \
       deps["dependencies"][0] == "<UNK>:interface":
        scaffolding += "friend " + module_name + "\n"
        needs_interface = True
    scaffolding += f"open {module_name}\n"    
    return (module_name, harness_name, extension, needs_interface, scaffolding)
    
def build_scaffolding(entry: Definition, deps: list[Dependency]):
    module_name, _harness_name, _extension, _needs_interface, scaffolding = build_file_scaffolding(deps)

    # add opens in reverse order
    # for each open in the entry, add an open statement to the scaffolding
    # iterate through entry["opens_and_abbrevs"] in reverse order
    # if oa["abbrev"] is defined then use it
    # otherwise use oa["open"]
    for oa in reversed(entry["opens_and_abbrevs"]):
        # if oa["abbrev"] is defined then use it
        # otherwise use oa["open"]
        if "abbrev" in oa:
            scaffolding += "module " + oa["key"] + "=" + oa["value"] + "\n"
        else:
            scaffolding += "open " + oa["open"] + "\n"
    scaffolding += "open " + module_name + "\n"

    #translate vconfig to an option string
    # for each key/value pair in vconfig, add an element to an array of strings with the key and value
    options = []
    for key, value in (entry["vconfig"] or {}).items():
        match key:
            case "z3cliopt" | "z3smtopt":
                for val in value:
                    options.append('--' + key)
                    options.append(f"'{val}'")
                continue
            case "initial_fuel" | "max_fuel" | "initial_ifuel" | "max_ifuel" | "z3rlimit" | "z3rlimit_factor" | "z3seed":
                value = str(value)
            case "z3refresh":
                if value:
                    options.append("--z3refresh")
                    continue
                else:
                    continue
            case "smtencoding_elim_box":
                key = "smtencoding.elim_box"
                if value:
                    value = "true"
                else:
                    value = "false"
            case "smtencoding_nl_arith_repr":
                key = "smtencoding.nl_arith_repr"
                value = str(value)
            case "smtencoding_l_arith_repr":
                key = "smtencoding.l_arith_repr"
                value = str(value)
            case "smtencoding_valid_intro":
                key = "smtencoding.valid_intro"
                if value:
                    value = "true"
                else:
                    value = "false"
            case "smtencoding_valid_elim":
                key = "smtencoding.valid_elim"
                if value:
                    value = "true"
                else:
                    value = "false"
            case (  "retry" |
                    "detail_errors" |
                    "reuse_hint_for" |
                    "no_plugins" |
                    "no_tactics" |
                    "no_smt" |
                    "quake_lo" |
                    "quake_hi" |
                    "quake_keep" |
                    "tcnorm" |
                    "trivial_pre_for_unannotated_effectful_fns" |
                    "detail_hint_replay" ):
                continue
            case _:
                continue        
        options.append("--" + key)
        options.append(str(value))
    # conatenate the options separated by spaces
    options_string = " ".join(options)
    # add the options string to the scaffolding
    scaffolding += f"#push-options \"{options_string}\"\n"
    #print (f"harness_name={harness_name}, extension={extension}, needs_interface={needs_interface}, scaffolding={scaffolding}, options={options}")
    return scaffolding

def process_one_instance(entry: Definition, deps: list[Dependency], fstar_process):
    if (entry["effect"] != "FStar.Pervasives.Lemma"):
        return
    #print("Attempting lemma " + entry["name"])
    scaffolding = build_scaffolding(entry, deps)
    lemma_long_name = entry["name"]
    lemma_name = lemma_long_name.split(".")[-1]
    if (lemma_name.startswith("__proj__")):
        return
    goal = entry["source_type"]
    if goal == "<UNK>" :
        goal = ""
    # NS: Here's where you should plug in a LLM-generated solution instead
    solution = entry["source_definition"]
    full_soln= f"{scaffolding}\n{goal}\n{solution}"
    # print(f"full_soln={full_soln}")
    result, detail = check_solution(fstar_process, full_soln)
    # the detail field contains the actual feedback, error report etc. from F* in case result==false
    logged_solution = { "name": lemma_long_name,
                        "goal_statement":goal,
                        "full_solution": full_soln,
                        "result": result,
                        "detail": detail }
    if result :
        print(f"Lemma {lemma_long_name} verified")
    else:
        print(f"Lemma {lemma_long_name} failed")
        print(full_soln)
    # append the logged solution to the json file as a json array
    return logged_solution

# for each entry in the json file, send the query to fstar insights
def send_queries_to_fstar(json_data, out_dir, out_file):
    outputs = []
    include = ["--include", 'dataset', '--include', out_dir] # TODO FIXME
    _module_name, harness_name, extension, needs_interface, static_scaffolding = build_file_scaffolding(json_data["dependencies"][0])
    fstar_process = launch_fstar(out_dir,include, harness_name, extension, static_scaffolding, needs_interface)    
    out_file = out_dir + "/" + out_file
    with open(out_file, "w") as f:
        deps = []
        # if json_data has a "dependencies" field
        if "dependencies" in json_data and len(json_data["dependencies"]) > 0:
            deps = json_data["dependencies"][0]
        # for each entry in the json file
        for entry in json_data["defs"]:
            # send the query to fstar insights
            sol = process_one_instance(entry, deps, fstar_process)
            if sol is not None:
                outputs.append(sol)
        json.dump(outputs, f, indent=4)


if __name__ == '__main__':
    # if the number of command line arguments is not 2, print an error message and exit
    # the first argument is the name of the script
    # the second argument is the name of the input json file
    # the third argument is the name of the output directory
    # the fourth argument is the name of the output file
    if len(sys.argv) != 4:
        print("Usage: python3 InteractWithFStar.py <json_file> <out dir> <out file>")
        exit(1)

    # read the json file specified on the first command line argument
    json_data: InsightFile = read_json_file(sys.argv[1])
    out_dir = sys.argv[2]
    out_file = sys.argv[3]
    send_queries_to_fstar(json_data, out_dir, out_file)