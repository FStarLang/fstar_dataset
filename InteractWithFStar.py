#!/usr/bin/env python3
import json
import sys
import FStarHarness as FH

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
    
def build_scaffolding(entry, deps):
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

def process_one_instance(entry, deps, fstar_process):
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
    result, detail = FH.check_solution(fstar_process, full_soln)
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
    fstar_process = FH.launch_fstar(out_dir,include, harness_name, extension, static_scaffolding, needs_interface)    
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
    json_data = read_json_file(sys.argv[1])
    out_dir = sys.argv[2]
    out_file = sys.argv[3]
    send_queries_to_fstar(json_data, out_dir, out_file)
