#!/usr/bin/env python3
from typing import TypedDict, Any, Optional, Callable, Iterable, Union, cast
import subprocess
import json
import sys
import os
import threading
import multiprocessing
import random
import queue

class Dependency(TypedDict):
    source_file: str
    checked_file: str
    interface_file: bool # Whether the file depends on its interface file
    dependencies: list[str]

class Open(TypedDict):
    open: str

class Abbrev(TypedDict):
    abbrev: str
    full_module: str

OpenOrAbbrev = Union[Open, Abbrev]

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
    z3smtopt: list[str]
    z3refresh: bool
    z3rlimit: int
    z3rlimit_factor: int
    z3seed: int
    z3version: str
    trivial_pre_for_unannotated_effectful_fns: bool
    reuse_hint_for: Optional[str]

class Range(TypedDict):
    file_name: str
    start_line: int
    start_col: int
    end_line: int
    end_col: int

class DefinitionToCheck(TypedDict):
    file_name: str # Filename where the definition logically appears (after interleaving)
    name: str # Fully-qualified name
    opens_and_abbrevs: list[OpenOrAbbrev]
    vconfig: Optional[Vconfig]
    source_type: str # val block
    source_definition: str # let block

class Definition(DefinitionToCheck):
    source_range: Range # The range where the definition's source code is located
    interleaved: bool # True if this definition was copied from the fsti file
    definition: str
    effect: str
    effect_flags: list[str]
    mutual_with: list[str]
    premises: list[str]
    proof_features: list[str]
    is_simple_lemma: bool
    type: str
    prompt: str
    expected_response: str

class Source(TypedDict):
    # Git repository name, e.g. `hacl-star`
    project_name: str
    # File name relative to the repository, e.g. `code/curve25519/Hacl.Impl.Curve25519.Lemmas.fst`
    file_name: str
    # Revision of the git repository
    git_rev: str
    # Url of the git repository
    git_url: str

class InsightFileFirstPass(TypedDict):
    defs: list[Definition]
    dependencies: Dependency

class InsightFile(InsightFileFirstPass):
    source: Source

def eprint(msg):
    sys.stderr.write(str(msg) + '\n')
    sys.stderr.flush()

class FStarIdeProcess:
    pushed_until_lid: Optional[str] = None

    def __init__(self, args: list[str]):
        self.process: Any = subprocess.Popen(
            args, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            # stderr=subprocess.PIPE,
            encoding='UTF-8')

        self.qid = 0

        # Consume initialization message
        res = self._read_msg()
        assert res['kind'] == 'protocol-info', res

    def __enter__(self): return self
    def __exit__(self, exc_type, exc_value, traceback):
        self.process.__exit__(exc_type, exc_value, traceback)

    def on_message(self, msg):
        if msg.get('level') != 'progress':
            eprint(msg['contents'])

    def _read_msg(self) -> Any:
        while True:
            line = self.process.stdout.readline()
            if line.startswith('{'):
                return json.loads(line)
            elif line == '':
                raise Exception(f'fstar terminated with exit code {self.process.poll()}')
            else:
                # fstar writes some --debug output to stdout.
                sys.stderr.write(line)

    def _write_msg(self, msg: Any):
        json.dump(msg, self.process.stdin)
        self.process.stdin.write('\n')
        self.process.stdin.flush()

    def _next_qid(self):
        self.qid += 1
        return str(self.qid)

    def call_simple(self, query: str, args: Any):
        qid = self._next_qid()
        self._write_msg({'query-id': qid, 'query': query, 'args': args})
        while True:
            res = self._read_msg()
            if res['kind'] == 'message':
                self.on_message(res)
            elif res['kind'] == 'response':
                assert res['query-id'] == qid, (res, qid)
                # eprint(f'result {json.dumps(res)}')
                return res
            else:
                raise Exception('Unexpected message from fstar: ' + json.dumps(res))

    def call_checked(self, query: str, args: Any):
        res = self.call_simple(query, args)
        assert res['status'] == 'success', res
        return res

    def pop_partial_checked(self):
        assert self.pushed_until_lid
        self.call_checked('pop', {})
        self.pushed_until_lid = None

    def load_partial_checked_until(self, until_lid: str):
        if self.pushed_until_lid:
            self.pop_partial_checked()
        self.call_checked('push-partial-checked-file', {'until-lid': until_lid})
        self.pushed_until_lid = until_lid

    def check_snippet_at_decl(self, decl_name: str, snippet: str) -> tuple[bool, Any]:
        self.load_partial_checked_until(decl_name)
        res = self.call_simple('push', {'kind': 'full', 'line': 0, 'column': 0, 'code': snippet})
        if res['status'] == 'success':
            self.call_checked('pop', {})
        success = res['status'] == 'success'
        if any(err['number'] == Warning_WarnOnUse for err in res['response']):
            success = False
        return success, res

Warning_WarnOnUse = 335

from dataclasses import dataclass

PoolTask = DefinitionToCheck

@dataclass
class TodoItem:
    task: PoolTask
    on_done: Callable[[Any], None]

    @property
    def file(self):
        return os.path.basename(self.task['file_name'])

    @property
    def defn(self):
        return self.task['name']

class FStarPool:
    mutex = threading.Lock()
    cv = threading.Condition(mutex)
    todo: dict[str, dict[str, list[TodoItem]]] = {}
    workers: list[threading.Thread]
    cur_worker_file: list[Optional[str]]
    cur_worker_defn: list[Optional[str]]
    _terminated: bool = False

    def __init__(self, dataset_dir: str, extra_args: list[str] = [], nworkers = None):
        if not nworkers: nworkers = multiprocessing.cpu_count()
        self.dataset_dir = dataset_dir
        self.extra_args = extra_args
        with self.mutex:
            self.cur_worker_file = [None] * nworkers
            self.cur_worker_defn = [None] * nworkers
            self.workers = []
            for i in range(nworkers):
                thr = threading.Thread(name=f'fstar-worker-{i}', target=self._worker, args=(i,), daemon=True)
                self.workers.append(thr)
                thr.start()

    def __enter__(self): return self
    def __exit__(self, exc_type, exc_value, traceback):
        self.close()

    def __del__(self):
        self.close()

    def close(self):
        with self.cv:
            if self._terminated: return
            self._terminated = True
            self.cv.notify_all()
        for thr in self.workers: thr.join()

    def _get_next(self, i):
        if len(self.todo) == 0: return None

        cur_file = self.cur_worker_file[i]
        cur_defn = self.cur_worker_defn[i]

        def go(f, d):
            item = self.todo[f][d].pop()
            if len(self.todo[f][d]) == 0:
                del self.todo[f][d]
            if len(self.todo[f]) == 0:
                del self.todo[f]
            return item

        if cur_file in self.todo:
            if cur_defn in self.todo[cur_file]:
                return go(cur_file, cur_defn)

            for d in self.todo[cur_file].keys():
                if d not in self.cur_worker_defn:
                    return go(cur_file, d)

            return go(cur_file, random.choice(list(self.todo[cur_file])))

        for f in self.todo.keys():
            if f not in self.cur_worker_file:
                return go(f, next(iter(self.todo[f].keys())))

        f = random.choice(list(self.todo))
        return go(f, random.choice(list(self.todo[f])))

    def _worker(self, i):
        cur_file: Optional[str] = None
        proc: Optional[FStarIdeProcess] = None

        while True:
            with self.cv:
                item = self._get_next(i)
                while item is None:
                    if self._terminated:
                        return
                    else:
                        self.cv.wait()
                        item = self._get_next(i)
                item_file = item.file
                self.cur_worker_defn[i] = item.task['name']
                self.cur_worker_file[i] = item_file

            if cur_file != item_file or proc is None:
                if proc is not None:
                    proc.process.terminate()
                proc = create_fstar_process_for_dataset(item_file, self.dataset_dir, self.extra_args)
                cur_file = item_file

            try:
                proc.load_partial_checked_until(item.task['name'])
                res = process_one_instance(item.task, proc)
                item.on_done(res)
            except BaseException as e:
                proc = None
                cur_file = None
                item.on_done(None)

    def _enqueue(self, item: TodoItem):
        item_file = item.file
        if item_file not in self.todo: self.todo[item_file] = {}
        if item.defn not in self.todo[item_file]: self.todo[item_file][item.defn] = []
        self.todo[item_file][item.defn].append(item)

    def _submit(self, items: Iterable[TodoItem]):
        with self.cv:
            for item in items:
                self._enqueue(item)
            self.cv.notify_all() # TODO: try to wake up workers with same file first

    def process_instances_unordered(self, tasks: list[PoolTask]) -> Iterable[tuple[PoolTask, Optional[Any]]]:
        q = queue.SimpleQueue()
        def mk_item(task: PoolTask) -> TodoItem:
            return TodoItem(on_done = lambda res: q.put((task, res)), task=task)
        self._submit(mk_item(task) for task in tasks)
        for _ in range(len(tasks)):
            yield q.get()

def build_scaffolding(entry: DefinitionToCheck):
    scaffolding = ''

    module_name = os.path.splitext(os.path.basename(entry["file_name"]))[0]
    if module_name == 'prims': module_name = 'Prims'

    if module_name != 'Prims':
        for oa in reversed(entry["opens_and_abbrevs"]):
            if "abbrev" in oa:
                scaffolding += "module " + oa["abbrev"] + "=" + oa["full_module"] + "\n"
            else:
                scaffolding += "open " + oa["open"] + "\n"

        # Necessary for FStar.Array where the local array should shadow the global one.
        scaffolding += "open " + module_name + "\n"

    #translate vconfig to an option string
    # for each key/value pair in vconfig, add an element to an array of strings with the key and value
    options = []
    for key, value in (entry["vconfig"] or {}).items():
        match key:
            case "z3cliopt" | "z3smtopt":
                for val in cast(list[str], value):
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
    return scaffolding

def process_one_instance(entry: DefinitionToCheck, fstar_process: FStarIdeProcess):
    scaffolding = build_scaffolding(entry)
    lemma_long_name = entry["name"]
    goal = entry["source_type"]
    if goal == "<UNK>" :
        goal = ""
    # NS: Here's where you should plug in a LLM-generated solution instead
    solution = entry["source_definition"]
    full_soln= f"{scaffolding}\n{goal}\n{solution}"
    result, detail = fstar_process.check_snippet_at_decl(entry['name'], full_soln)
    # the detail field contains the actual feedback, error report etc. from F* in case result==false
    logged_solution = { "name": lemma_long_name,
                        "goal_statement":goal,
                        "full_solution": full_soln,
                        "result": result,
                        "detail": detail }
    # append the logged solution to the json file as a json array
    return logged_solution

def should_ignore(entry: Definition) -> Optional[str]:
    if entry['interleaved']:
        return 'interleaved'
    if entry['definition'].startswith('<'):
        return 'nondefinition'
    if '=' not in entry['source_definition']:
        # QueryCheckedFile messages up `type =` declarations.
        return 'nondefinition (type)'
    if entry['file_name'] == 'dummy':
        return 'unreal lemma'
    return None

def create_fstar_process_for_dataset(file_name: str, dataset_dir: str, extra_args: list[str] = []) -> FStarIdeProcess:
    return FStarIdeProcess(["fstar.exe",
        "--ide", os.path.basename(file_name),
        "--report_assumes", "warn", '--include', dataset_dir] + extra_args)

def create_fstar_process_for_json_file(json_data: InsightFile, dataset_dir: str, extra_args: list[str] = []) -> FStarIdeProcess:
    return create_fstar_process_for_dataset(json_data['dependencies']['source_file'], dataset_dir, extra_args)

# for each entry in the json file, send the query to fstar insights
def send_queries_to_fstar(json_data: InsightFile, dataset_dir: str):
    outputs = []
    extra_args = [
        # '--trace_error',
        # '--debug', 'FStar.Array',
        # '--debug_level', 'Rel,RelCheck,High',
    ]
    with create_fstar_process_for_json_file(json_data, dataset_dir, *extra_args) as fstar_process:
        # for each entry in the json file
        for entry in json_data["defs"]:
            if reason := should_ignore(entry):
                # eprint(f'Ignoring {entry["name"]}: {reason}')
                continue
            # send the query to fstar insights
            out = process_one_instance(entry, fstar_process)
            # if out['result']:
            #     eprint(f'Verified {out["name"]}')
            # else:
            #     eprint(f'Failed {out["name"]}')
            outputs.append(out)
        return outputs

def pool_tasks_of_file(json_data: InsightFile, warn=False) -> list[PoolTask]:
    items: list[PoolTask] = []
    for entry in json_data["defs"]:
        if reason := should_ignore(entry):
            if warn: eprint(f'Ignoring {entry["name"]}: {reason}')
            continue
        items.append(entry)
    return items

if __name__ == '__main__':
    import tqdm

    if len(sys.argv) < 2:
        sys.stderr.write('Usage: python3 fstar_harness.py dir/dataset Input.File1.json Input.File2.json ...\n')
        exit(1)
    dataset_dir, *input_files = sys.argv[1:]

    tasks = []
    for f in input_files:
        j: InsightFile = json.load(open(f))
        tasks += pool_tasks_of_file(j)

    extra_args = [
        # '--trace_error',
        # '--debug', 'FStar.Array',
        # '--debug_level', 'Rel,RelCheck,High',
    ]
    with FStarPool(dataset_dir, extra_args) as pool:
        outputs = [ res[1] for res in tqdm.tqdm(pool.process_instances_unordered(tasks), total=len(tasks)) ]
    json.dump(outputs, sys.stdout)
    sys.stdout.write('\n')
