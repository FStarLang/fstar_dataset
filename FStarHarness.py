
import sys
import subprocess
import json

# Note: Can we add an option to F* to only load a prefix of a given checked file?
# we want to prevent a candidate proof from relying on out-of-scope parts of an F* checked file
# notably the part including or following the definition/proof we're trying to synthesize
def generate_harness_for_lemma(out_dir, harness_name, extension, scaffolding, needs_interface):
    # Write scaffoling to a file names Harness.module_name.fst
    file_name = harness_name + "." + extension
    file_name = out_dir + "/" + file_name
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
    fstar_args = ["fstar.exe", "--ide", file_name, "--report_assumes", "warn"]
    for i in options:
        fstar_args.append(i)
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

def check_solution(fstar_process, solution):
    code = json.dumps(solution)
    request = f'{{"query-id":"2", "query": "full-buffer", "args":{{"kind": "full", "with-symbols":false, "code": {code}, "line":1, "column":0}}}}\n'
    check_wf = json.loads(request)
    #print(f'Asking F* to check solution: {request}')
    fstar_process.stdin.write(json.dumps(check_wf))
    fstar_process.stdin.write("\n")
    fstar_process.stdin.flush()
    # Read the response from stdout
    response_objects = read_full_buffer_response(fstar_process)
    # Validate the response
    return validate_fstar_response(response_objects)
