import argparse
import os
import traceback
import tqdm
import json
from multiprocessing import Pool

from fstar_harness import create_fstar_process_for_dataset, analyze_solution

DATSET_DIR = "dataset"


def evaluation_function(truths):
    if truths is None or len(truths) == 0:
        truths = [False]
    k_values = range(1, len(truths) + 1)
    metrics = {
        f"pass@{k}": any(truths[:k]) for k in k_values
    }
    metrics["pass@any"] = any(truths)
    return metrics


def remove_block_comment(response):
    if "(*" in response:
        first_part = response[:response.index("(*")]
        second_part = response[response.index("(*") + 2:]
        if "*)" in second_part:
            remaining = second_part[second_part.index("*)") + 2:]
        else:
            remaining = ""
        response = first_part + remaining
        return remove_block_comment(response)
    return response


def remove_line_comment(response):
    lines = response.split("\n")
    taken_lines = []
    for l in lines:
        if "//" in l:
            l = l[:l.index("//")]
            if l.strip() != "":
                taken_lines.append(l)
        else:
            taken_lines.append(l)
    return "\n".join(taken_lines)


def sanitize(response):
    response = remove_block_comment(response)
    response = remove_line_comment(response)
    return response


def check_example(inp):
    example, check_ground_truth, solution_key, timeout = inp
    name = example["name"]
    if "." in name:
        name = name.split(".")[-1]

    if check_ground_truth:
        responses = [example["source_definition"]]
    else:
        solution_key_parts = solution_key.split("/")
        responses = example
        for k in solution_key_parts:
            responses = responses[k]
        assert isinstance(responses, list) or isinstance(responses, str)
        if isinstance(responses, str):
            responses = [responses]
        responses = [sanitize(r) for r in responses]
    results = [None] * len(responses)
    truths = [False] * len(responses)
    for ri, response in enumerate(responses):
        proc = create_fstar_process_for_dataset(
            example["file_name"], DATSET_DIR, [], timeout=timeout
        )
        try:
            proc.load_partial_checked_until(example['name'])
            goal_stmt = example["original_source_type"]
            goal_stmt = goal_stmt.strip()
            if goal_stmt == "" or goal_stmt == "<UNK>":
                goal_stmt = f""
            res = analyze_solution(
                entry=example,
                goal_statement=goal_stmt,
                solution=response,
                fstar_process=proc,
                check_name_match=not check_ground_truth
            )
            res["checked_solution"] = response
            results[ri] = res
            truths[ri] = res["result"] if res is not None else False
        except Exception as e:
            traceback.print_exc()
            proc.process.terminate()
            if isinstance(e, KeyboardInterrupt):
                raise e
            res = None
            results[ri] = res
            truths[ri] = False
        if proc is not None:
            proc.process.terminate()
    return (example, results, truths, evaluation_function(truths))


def summarize_metrics(metrics_list):
    summary = {}
    for metric in metrics_list[0]:
        values = [m[metric] if metric in m else False for m in metrics_list]
        summary[metric] = round((sum(values) * 100 / len(values)), 2)
    return summary


def get_argument():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input_files", "-i", type=str,
                        required=True, nargs="+")
    parser.add_argument("--dataset_dir", "-s", type=str, required=True)
    parser.add_argument("--output", "-o", type=str, default=None)
    parser.add_argument("--output_dir", "-d", type=str)
    parser.add_argument("--check_ground_truth", "-g", action="store_true")
    parser.add_argument("--solution_key", "-k", type=str,
                        default="generated_response/responses")
    parser.add_argument("--timeout", "-t", type=float, default=100000)
    parser.add_argument("--num_workers", "-w", type=int, default=80)
    return parser.parse_args()


def main():
    args = get_argument()
    assert args.dataset_dir is not None and os.path.exists(
        args.dataset_dir), "Dataset directory not found."
    global DATSET_DIR
    DATSET_DIR = args.dataset_dir

    generated_files = args.input_files
    tasks = []
    for gf in generated_files:
        with open(gf, "r") as fp:
            tasks.extend(json.load(fp))
            fp.close()
    tasks = [(t, args.check_ground_truth, args.solution_key, args.timeout)
             for t in tasks]
    pool = Pool(
        args.num_workers) if args.num_workers is not None and args.num_workers > 1 else None
    mapping_function = pool.imap_unordered if pool is not None else map
    results = mapping_function(check_example, tasks)
    detailed_results, aggregate_metrics = [], []
    bar = tqdm.tqdm(results, total=len(tasks), desc="")
    for example, res, truths, metrics in bar:
        detailed_results.append(
            {"example": example, "results": res, "truths": truths, "metrics": metrics})
        aggregate_metrics.append(metrics)
        bar.set_description(json.dumps(summarize_metrics(aggregate_metrics)))
    if pool:
        pool.close()

    final_summary_metrics = summarize_metrics(aggregate_metrics)
    print(json.dumps(final_summary_metrics, indent=4))
    if args.output_dir is not None:
        if len(generated_files) > 1:
            assert args.output is not None, "Output file must be specified when multiple input files are provided."
        output_file_name = os.path.basename(args.input_files[0]) if len(
            args.input_files) == 1 else args.output
        os.makedirs(args.output_dir, exist_ok=True)
        with open(os.path.join(args.output_dir, output_file_name.replace(".json", "_detailed_results.json")), "w") as fp:
            json.dump(detailed_results, fp, indent=4)
            fp.close()
        with open(os.path.join(args.output_dir, output_file_name.replace(".json", "_aggregate_metrics.json")), "w") as fp:
            json.dump(aggregate_metrics, fp, indent=4)
            fp.close()
        with open(os.path.join(args.output_dir, output_file_name.replace(".json", "_summary_metrics.json")), "w") as fp:
            json.dump(final_summary_metrics, fp, indent=4)


if __name__ == "__main__":
    main()
