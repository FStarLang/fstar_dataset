import subprocess
import json
fstar_process = subprocess.Popen(["fstar.exe", "--ide", "Scaffolding.fst"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
fstar_process.stdin.write(f'{{"query-id":"1", "query": "vfs-add", "args":{{"filename":null, "contents": "module Scaffolding"}}}}\n')
fstar_process.stdin.flush()

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
def generate_scaffolding(bench):
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

# A function to validate the response from F* interactive mode
def validate_fstar_response(json_objects, contents):
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
def read_full_buffer_response():
    response = ""
    json_objects = []
    while True:
        line = fstar_process.stdout.readline()
        # print("Line from F*: " + line)
        response = response + line
        resp = json.loads(line)
        json_objects.append(resp)
        if resp["kind"] == "message" and resp["level"] == "progress" and resp["contents"] is not None:
            if resp["contents"]["stage"] == "full-buffer-finished":
                break
    # print ("Response from F*: " + response)
    return json_objects

# Launch an F* process for a benchmark and a given solution string
def check_with_fstar(bench, solution):
    (scaffolding, sol) = generate_scaffolding(bench)
    contents = scaffolding + sol + solution + "\n"
    json_contents = json.dumps(contents)
    request = f'{{"query-id":"2", "query": "full-buffer", "args":{{"kind": "full", "with-symbols":false, "code": {json_contents}, "line":1, "column":0}}}}\n'
    fstar_process.stdin.write(request)
    fstar_process.stdin.flush()
    # Read the response from stdout
    response_objects = read_full_buffer_response()
    # Validate the response
    return validate_fstar_response(response_objects, contents)

