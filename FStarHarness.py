
import sys
import subprocess
import json
# A sample scaffoling from a benchmark instance
# { id:1,
#   types: [ "t1", "t2" ],
#   functions: [ ("f1", "t1 -> t2"), ("f2", "t2 -> t3") ],
#   goal: "t1 -> t3",
#   solutions: [ "compose f2 f1" ],
# }
# The scaffolding is
# module Scaffolding
# assume val t1 : Type0
# assume val t2 : Type0
# assume val f1 : t1 -> t2
# assume val f2 : t2 -> t3
# let solution : t1 -> t3 =

# Generate the scaffolding for a benchmark instance
def generate_scaffolding_for_function_composition(bench):
    scaffolding = """
        module Scaffolding\n
        assume val compose (f:'b -> 'c) (g:'a -> 'b) : 'a -> 'c\n"""
    types = bench["types"]
    functions = bench["functions"]
    for t in types:
        type_decl = "assume val " + t + " : Type0\n"
        scaffolding = scaffolding + type_decl
    for (f, t) in functions:
        function_decl = "assume val " + f + " : " + t + "\n"
        scaffolding = scaffolding + function_decl
    solution = "let solution : " + bench["goal"] + " = "
    return (scaffolding, solution)

def generate_harness_for_lemma(module_name, deps, target_lemma):
    scaffolding = "module Harness." + module_name + "\n"
    for d in deps:
        scaffolding = scaffolding + "open " + d + "\n"
    scaffolding = scaffolding + target_lemma
    # Write scaffoling to a file names Harness.module_name.fst
    file_name = "Harness." + module_name + ".fst"
    with open(file_name, "w") as f:
        f.write(scaffolding)
    return (file_name, scaffolding)

# Launch an F* process in interactive mode
def launch_fstar(file_name):
    fstar_process = subprocess.Popen(["fstar.exe", "--ide", file_name, "--report_assumes", "warn"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
    # # read the contents of file_name into a string
    # with open(file_name, "r") as f:
    #     contents = f.read()
    # fstar_process.stdin.write(f'{{"query-id":"1", "query": "vfs-add", "args":{{"filename":null, "contents": "{contents}"}}}}\n')
    # fstar_process.stdin.flush()
    # # Read the response from stdout
    # pinfo = fstar_process.stdout.readline()
    # print("F* process info: " + pinfo)
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
                return False
            else:
                continue
        print(f"Error: {resp}")
        return False
    return True


# read the response from stdout
# until we get a line with kind=message and args.kind=full-buffer-finished
def read_full_buffer_response(fstar_process):
    response = ""
    json_objects = []
    while True:
        if fstar_process.poll() is not None:
            print("F* process terminated")
            break
        line = fstar_process.stdout.readline()
        # print a line to stderr for debugging
        print("Line from F*: " + line, file=sys.stderr)
        response = response + line
        resp = json.loads(line)
        json_objects.append(resp)
        if resp["kind"] == "message" and resp["level"] == "progress" and resp["contents"] is not None:
            if resp["contents"]["stage"] == "full-buffer-finished":
                break
    # print ("Response from F*: " + response)
    return json_objects

def check_solution(fstar_process, solution):
    code = json.dumps(solution)
    request = f'{{"query-id":"2", "query": "full-buffer", "args":{{"kind": "full", "with-symbols":false, "code": {code}, "line":1, "column":0}}}}\n'
    check_wf = json.loads(request)
    print(f'Asking F* to check solution: {request}')
    fstar_process.stdin.write(json.dumps(check_wf))
    fstar_process.stdin.write("\n")
    fstar_process.stdin.flush()
    # Read the response from stdout
    response_objects = read_full_buffer_response(fstar_process)
    # Validate the response
    return validate_fstar_response(response_objects)

# # Launch an F* process for a benchmark and a given solution string
# def check_function_comp_with_fstar(bench, solution):
#     (scaffolding, sol) = generate_scaffolding_for_function_composition(bench)
#     contents = scaffolding + sol + solution + "\n"
#     json_contents = json.dumps(contents)
#     request = f'{{"query-id":"2", "query": "full-buffer", "args":{{"kind": "full", "with-symbols":false, "code": {json_contents}, "line":1, "column":0}}}}\n'
#     fstar_process.stdin.write(request)
#     fstar_process.stdin.flush()
#     # Read the response from stdout
    response_objects = read_full_buffer_response()
    # Validate the response
    return validate_fstar_response(response_objects, contents)

