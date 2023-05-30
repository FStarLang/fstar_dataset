import json
import subprocess
import os
import sys
import openai
import re
import tiktoken
from tenacity import (
    retry,
    stop_after_attempt,
    wait_exponential,
    wait_random_exponential,
    retry_if_exception_type
) 

encoding = tiktoken.encoding_for_model("gpt-3.5-turbo")
openai.api_type = "azure"
openai.api_key = os.getenv("OPENAI_API_KEY")
openai.api_base = os.getenv("OPENAI_API_BASE")
openai.api_version = os.getenv("OPENAI_API_VERSION")

def maybe_extend_prompt(prompt, rest_of_prompt, config):
    next_prompt = prompt + "\n" +rest_of_prompt
    encoded_prompt = encoding.encode(next_prompt)
    if len(encoded_prompt) < config["input_token_limit"]:
        return next_prompt
    else:
        return None

@retry(wait=wait_random_exponential(min=1, max=60), stop=stop_after_attempt(100), retry=retry_if_exception_type(openai.error.RateLimitError))
def call_model(prompt, config):
    try:
        result = openai.ChatCompletion.create(
            engine= config["engine"],
            messages=[{"role": "system", "content": "Pretend you are an F* proof assistant. Provide a proof to the best of your ability. You do not need to explain the output, please be brief."},{"role": "user", "content": prompt}],
            max_tokens=config["output_token_limit"],
            temperature=config["temperature"],
            n = config["num_attempts"],
        )
        return result.choices
    except Exception as e:
        return "<model parameter error>"

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
        try:
            text = get_text_between_positions(file_name, start_line, start_column, end_line, end_column)
            #print(f'Text between positions: {file_name}@{start_line},{start_column}-{end_line},{end_column}=\n{text}\n')
            content.append(text)
        except:
            #content not found; just skip
            continue
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
        # print ("Response from fstar insights: " + line)
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

def prepare_prompt(context, lemma_name, goal, config):
    prompt = "This is a problem in the F* programming language.\n\n Can you write a proof of the goal lemma below?\n\n"
    prompt += "\n\nYou can use some other lemmas and functions in the context, <CONTEXT>\n\n"
    while len(context) > 0:
        extended_prompt = maybe_extend_prompt(prompt, context.pop(0), config)
        if extended_prompt is None:
            break
        else:
            prompt = extended_prompt
    prompt += "\n\n</CONTEXT>\n\n"
    prompt += "The goal is <GOAL>\n\n val " + lemma_name + " : " + goal + "\n\n</GOAL>\n\n"
   # prompt += "Your solution should look like this: let " + lemma_name + " = <YOUR PROOF HERE>\n\n"
    prompt += "Surround your proof with <PROOF> and </PROOF> tags.\n\n"
    print("<SAMPLE PROMPT>" +prompt+ "</SAMPLE PROMPT>")
    return prompt

def process_one_instance(fstar_insights_process, entry, config, out_file):
    print("Attempting lemma " + entry["name"])
    lemma_long_name = entry["name"]
    lemma_name = lemma_long_name.split(".")[-1]
    (context, goal) = send_one_query_to_fstar_insights(fstar_insights_process, entry)
    # print(f'Context: {context}\n\n Goal is: {goal}\n')
    module_name = entry["source_file"]
    # strip the .fst extension
    module_name = module_name[:-4]
    lemma_statement = entry["lemma_statement"]
    goal_statement = f'val {lemma_name} : {lemma_statement}'
    file_name, scaffolding = FH.generate_harness_for_lemma(module_name, [module_name], goal_statement)
    fstar_process = FH.launch_fstar(file_name)
    #for attempt in range(config["num_attempts"]):
    prompt = prepare_prompt(context, lemma_name, goal, config) 
    proposed_solution = call_model(prompt, config)
    
    for i, solution in enumerate(proposed_solution):
        solution_text = solution['message']['content']
        solution_text = solution_text[solution_text.find("<PROOF>")+len("<PROOF>"):solution_text.find("</PROOF>")]
        solution = f'{scaffolding}\n{solution_text}\n'
        should_check_result="no-check"
        if (config["should_check"]):
            should_check_result = FH.check_solution(fstar_process, solution)
        logged_solution = { "attempt": i, "prompt":prompt, "solution":solution_text, "entry":entry, "check_result":should_check_result }
        json.dump(logged_solution, out_file)

    # print(f'Got result {result}')
# for each entry in the json file, send the query to fstar insights
def send_queries_to_fstar_insights(fstar_insights_process, json_data, config):
    with open(out_file, "w") as f:
        # for each entry in the json file
        for entry in json_data:
            # send the query to fstar insights
            process_one_instance(fstar_insights_process, entry, config, f)

# if the number of command line arguments is not 2, print an error message and exit
# the first argument is the name of the script
# the second argument is the name of the json file
if len(sys.argv) != 3:
    print("Usage: python3 fstar_insights.py <json_file> <out file>")
    exit(1)

# read the json file specified on the first command line argument
json_data = read_json_file(sys.argv[1])
config = read_json_file("interact_with_fstar.config.json")
out_file = sys.argv[2]
fstar_insights_process = launch_fstar_insights()
send_queries_to_fstar_insights(fstar_insights_process, json_data, config)
fstar_insights_process.stdin.close()

