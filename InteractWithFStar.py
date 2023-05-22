import json
import subprocess
import os
import sys
import openai

openai.api_key = os.getenv("OPENAI_API_KEY")

def call_model(prompt): 
    result = openai.Completion.create(
        model="text-davinci-003",
        prompt=prompt,
        max_tokens=1024,
        temperature=0.2
    )
    print(result)
    return result.choices[0].text

#call_model ("Tell me a joke")


fstar_insights_exe="fstar_insights/ocaml/bin/fstar_insights.exe"
# read the environment variable FSTAR_HOME
fstar_home = os.environ.get("FSTAR_HOME")
# if fstar_home is None set it to the current directory
if fstar_home is None:
    fstar_home = os.getcwd()
    # concatenate "../everest/FStar" to fstar_home
    fstar_home = os.path.join(fstar_home, "../everest/FStar")

includes = [os.path.join(fstar_home, "ulib/.cache"), os.path.join(fstar_home, "ulib") ]
# for each element in includes add it to the include path preceded by "--include"
include_path = []
for path in includes:
    include_path.append("--include")
    include_path.append(path)

# Read the json file
def read_json_file(filename):
    # open the file and read its contents
    with open(filename) as f:
        data = json.load(f)
    return data

# launch fstar insights and return the process
def launch_fstar_insights():
    options = [fstar_insights_exe, "--interactive"]
    # add the include path to the options
    options.extend(include_path)
    # print the options
    print ("Launching fstar insights with options:")
    print(options)
    # redirect stderr to the stderr of the current process
    # stderr = subprocess.STDERR
    # launch fstar insights
    fstar_insights_process = subprocess.Popen(options, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
    return fstar_insights_process

# A map from file names to file contents
file_contents = {}

# open a file and read its contents, store the contents in the map
def read_file_contents(file_name):
    # check if the file is already in the map
    if file_name in file_contents:
        return
    # search for the file in the include path
    full_path = None
    for path in includes:
        # concatenate the path and the file name
        full_path = os.path.join(path, file_name)
        # if the file exists, break
        if os.path.exists(full_path):
            break
    # if the file does not exist, raise an exception
    if not os.path.exists(full_path):
        raise Exception("File " + file_name + " not found in the include path.")
    # open the file and read its contents
    with open(full_path) as f:
        contents = f.read()
    # store the contents in the map
    file_contents[file_name] = contents

# given a file, a start line and a start column, and an end line and an end column, return the text between the start and end positions
def get_text_between_positions(file_name, start_line, start_column, end_line, end_column):
    # start_line and end_line are 1-based
    # start_column and end_column are 0-based
    # start_line = start_line - 1
    # read the file contents
    read_file_contents(file_name)
    # get the contents of the file
    contents = file_contents[file_name]
    # split the contents into lines
    lines = contents.split("\n")
    # get the start line
    start_line_contents = lines[start_line - 1]
    # get the end line
    end_line_contents = lines[end_line - 1]
    # get the text between the start and end positions
    text = start_line_contents[start_column:]
    # if the start and end lines are the same, then we are done
    if start_line == end_line:
        # return the text between the start and end positions
        return text[:end_column - start_column]
    # otherwise, we need to add the text from the intermediate lines
    for i in range(start_line + 1, end_line):
        # add the line to the text
        text = text + "\n" + lines[i - 1]
    # add the end line
    text = text + "\n" + end_line_contents[:end_column]
    # return the text
    return text
    
def process_response(resp):
    content = []
    for entry in resp:
        file_name = entry["file_name"]
        start_line = entry["start_line"]
        start_column = entry["start_col"]
        end_line = entry["end_line"]
        end_column = entry["end_col"]
        text = get_text_between_positions(file_name, start_line, start_column, end_line, end_column)
        #print(f'Text between positions: {file_name}@{start_line},{start_column}-{end_line},{end_column}=\n{text}\n')
        content.append(text)
    return content

# for each entry in the json file, send the query to fstar insights
def send_one_query_to_fstar_insights(fstar_insights_process, entry):
    # print the entry       
    # print(entry) 
    payload = f'{{"source_file":"{entry["source_file"]}", "name": "{entry["name"]}"}}'
    fstar_insights_process.stdin.write(f'{{"command":"find_deps", "payload": {payload}}}\n')
    # fstar_insights_process.stdin.write(json.dumps(entry))
    # fstar_insights_process.stdin.write("\n")
    fstar_insights_process.stdin.flush()
    # # print all the output from stdout and close the process
    # print(fstar_insights_process.stdout.read())
    # fstar_insights_process.stdin.close()
    # read all the response from stdout until we get a line that parses as json
    resp = None
    while True:
        # check if the process is still running
        if fstar_insights_process.poll() is not None:
            print("fstar insights process is not running anymore")
            break
        # read a line from stdout, until the end 
        line = fstar_insights_process.stdout.readline()
        print ("Response from fstar insights: " + line)
        try:
            resp = json.loads(line)
            break
        except:
            print("Not json, keeping on reading")
    context = process_response(resp)
    goal = entry["lemma_statement"]
    # print(f'Context: {context}\n|- {goal}\n')
    return (context, goal)

import FStarHarness as FH

def prepare_prompt(context, goal):
    prompt = "This is a problem in the F* programming language.\n\n Can you write a proof of the goal lemma below?\n\n"
    prompt += "The goal is <GOAL>\n\n val goal : " + goal + "\n\n</GOAL>\n\n"
    prompt += "\n\nYou can use some other lemmas and functions in the context, <CONTEXT>\n\n"
    while (len(prompt) < 1024 and len(context) > 0):
        prompt = prompt + context.pop(0) + "\n"
    prompt += "\n\n</CONTEXT>\n\n"
    prompt += "Your solution should look like this: let goal = <YOUR PROOF HERE>\n\n"
    print("<SAMPLE PROMPT>" +prompt+ "</SAMPLE PROMPT>")
    return prompt

def process_one_instance(fstar_insights_process, entry):
    print("Attempting lemma " + entry["name"])
    (context, goal) = send_one_query_to_fstar_insights(fstar_insights_process, entry)
    print(f'Context: {context}\n\n Goal is: {goal}\n')
    module_name = entry["source_file"]
    # strip the .fst extension
    module_name = module_name[:-4]
    lemma_statement = entry["lemma_statement"]
    goal_statement = f'val goal : {lemma_statement}'
    file_name, scaffolding = FH.generate_harness_for_lemma(module_name, [module_name], goal_statement)
    fstar_process = FH.launch_fstar(file_name)  
    prompt = prepare_prompt(context, goal) 
    proposed_solution = call_model(prompt) #"let goal = admit()\n" #instead of placeholder, get a suggestion from LLM
    solution = f'{scaffolding}\n{proposed_solution}\n'
    result = FH.check_solution(fstar_process, solution)
    print(f'Got result {result}')

# for each entry in the json file, send the query to fstar insights
def send_queries_to_fstar_insights(fstar_insights_process, json_data):
    # for each entry in the json file
    for entry in json_data:
        # send the query to fstar insights
        process_one_instance(fstar_insights_process, entry)

# if the number of command line arguments is not 2, print an error message and exit
# the first argument is the name of the script
# the second argument is the name of the json file
if len(sys.argv) != 2:
    print("Usage: python3 fstar_insights.py <json_file>")
    exit(1)
     
# read the json file specified on the first command line argument
json_data = read_json_file(sys.argv[1])
# launch fstar insights
fstar_insights_process = launch_fstar_insights()
# send the queries to fstar insights
send_queries_to_fstar_insights(fstar_insights_process, json_data)
# close the process
fstar_insights_process.stdin.close()