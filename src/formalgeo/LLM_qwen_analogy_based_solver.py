import json
import os
import argparse
import logging
import sys
import io
from formalgeo.data import download_dataset, DatasetLoader
from formalgeo.solver import Interactor
from formalgeo.parse import parse_one_theorem
import pandas as pd
from Problem import get_theorem, replace_symbols
from create_problems_proofs_similarity_dataset import save_problems
import time
import requests

import traceback
from src.formalgeo.verifier import Verifier

from geometric_verifier import verify_geometric_proof
from src.formalgeo.config.config import MAX_RETRIES_IN_RUN, MAX_RUNS, SIMILAR_PROBLEMS, IN_CONTEXT_FEW_SHOT, \
    SAMPLED_PROBLEMS_IN_LEVEL, MIN_LEVEL, MAX_LEVEL

from similar_proofs_retrieval import retrieve_similar_proofs
from similar_proofs_retrieval import retrieve_random_proofs

# Get the path to the project root
PROJECT_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))

# --- Qwen client setup ---
# Set these via environment variables or pass --api_base / --api_key on the CLI.
#
# Ollama (default - local):
#   ollama pull qwen3:8b
#   ollama serve   (or: brew services start ollama)
#   # API is at http://localhost:11434/v1
#
# Local vLLM example (Linux + GPU):
#   python -m vllm.entrypoints.openai.api_server --model Qwen/Qwen3-8B --port 8000
#   export QWEN_API_BASE=http://localhost:8000/v1
#   export QWEN_API_KEY=EMPTY
#
# Together AI example:
#   export QWEN_API_BASE=https://api.together.xyz/v1
#   export QWEN_API_KEY=<your-together-key>
#
# Alibaba DashScope example:
#   export QWEN_API_BASE=https://dashscope.aliyuncs.com/compatible-mode/v1
#   export QWEN_API_KEY=<your-dashscope-key>

QWEN_API_BASE = os.environ.get("QWEN_API_BASE", "http://localhost:11434/v1")
QWEN_API_KEY = os.environ.get("QWEN_API_KEY", "ollama")


dl = DatasetLoader(dataset_name="formalgeo7k_v1", datasets_path=os.path.join(PROJECT_ROOT, "formalgeo7k_v1"))
solver = Interactor(dl.predicate_GDL, dl.theorem_GDL)
with open(os.path.join(PROJECT_ROOT, 'formalgeo7k_v1/gdl/theorem_GDL.json'), 'r') as f:
    theorems = json.load(f)


chosen_problems_by_level = {
    # 3: [4187] #  2795, 1168, 2677, 380, 944, 2940],
     # 1: [1975, 1490, 1726, 178, 2669, 2614, 51, 2323, 192, 2624, 2795, 1168, 688, 2677, 380, 221, 944, 2940, 2187, 1562],
     # 2: [144, 69, 991, 358, 4473, 4483, 5645, 127, 2410, 4523, 3075, 49, 4610, 6966, 1433, 3998, 5983, 497, 1586, 2397],
     # 3: [4187, 5244, 5062, 844, 1945, 2200, 4099, 2765, 4476, 4254, 1071, 3787, 4257, 5942, 1282, 2591, 5858, 1306, 1244, 312],
     # 4: [2114, 464, 5510, 3272, 5230, 3634, 6924, 4797, 5399, 6155, 4318, 4801, 4062, 6021, 1872, 4705, 2543, 4199, 6641, 5200],
     # 5: [5440, 6485, 696, 847, 5563, 532, 5431, 437, 5080, 6660, 6615, 3210, 2556, 5777, 3705, 4096, 1855, 5101, 5642, 4170],
     # 6: [4923, 3298, 759, 4910, 5805, 5708, 6417, 5835, 5808, 5779, 6398, 424, 4666, 6743, 5665, 6440, 3462, 5505, 5834, 4945],
     # 7: [3580, 4898, 6802, 6247, 449, 1854, 5208, 6322, 3412, 3027, 6330, 6644, 6147, 6932, 929, 3859, 5426, 1571, 3891, 4306],
     # 8: [6760, 3983, 2761, 2875, 3434, 1258, 246, 6806, 4793, 2106, 4736, 4816, 5379, 6598, 6401, 5531, 2917, 1858, 4549, 5022],
     # 9: [4892, 5092, 5522, 4796, 3418, 6850, 6790, 5116, 2851, 716, 6491, 6026, 4250, 6889, 5497, 429, 4932, 6840, 4481, 3249],
     # 10: [4134, 3419, 2196, 4489, 6146, 6018, 6376, 5353, 3114, 5197, 4672, 4465, 3840, 6549, 5181, 6024, 4888, 392, 6239, 2371],
}


def get_theorem_seqs_expl(theorem_seqs):
    theorems_seqs_expl = []
    for theorem in theorem_seqs:
        t_name, t_branch, t_para = parse_one_theorem(theorem)
        letters = get_letters(t_name, t_para)
        theory_json = get_theorem(theorem)
        premise, conclusions = json.loads(theory_json)['premise'], json.loads(theory_json)['conclusion']
        premise = replace_symbols(premise, letters)
        if isinstance(conclusions, str):
            conclusions = [conclusions]
        for i in range(len(conclusions)):
            conclusions[i] = replace_symbols(conclusions[i], letters)

        updated_json = {
            "theorem": theorem,
            "premise": premise,
            "conclusion": conclusions
        }
        updated_json_str = json.dumps(updated_json, indent=4)
        theorems_seqs_expl.append(updated_json_str)
    return theorems_seqs_expl


def get_letters(t_name, t_para):
    letters = {}
    for i in range(len(solver.parsed_theorem_GDL[t_name]["vars"])):
        key = solver.parsed_theorem_GDL[t_name]["vars"][i].upper()
        letters[key] = t_para[i]
    return letters


def remove_trailing_empty_lines(text):
    return '\n'.join(line for line in text.splitlines() if line.strip())


def convert_relations(relations_string):
    relations_list = relations_string.split("\n")
    res = []
    type = ""
    for row in relations_list:
        if not row.startswith("("):
            type = row[:-1]
        else:
            values = row.split(";")
            res.append((type + "(" + values[1] + ")", values[-1][:-1]))
    extended_res = []
    for tup in res:
        if tup[-1] == "prerequisite":
            continue
        extended_res.append(tup[0])
    return "\n".join(extended_res)




def theorem_verifier(solver, theorem_seqs):
    res = "Correct"
    for theorem in theorem_seqs:
        t_name, t_branch, t_para = parse_one_theorem(theorem)
        letters = get_letters(t_name, t_para)
        theory_json = get_theorem(theorem)
        premise = json.loads(theory_json)['premise']
        premise = replace_symbols(premise, letters)
        update, reason = solver.apply_theorem(t_name, t_branch, t_para)
        if not update and reason != 'No updates were made.':
            return "A mistake in theorem sequence step: " + theorem + ". Premise: " + premise + ". " + reason
    return res


# ---------------------------------------------------------------------------
#  Qwen model call  (replaces call_gpt_o1 / call_gpt from the GPT solver)
# ---------------------------------------------------------------------------

def call_qwen(model, messages, temperature=0.7, max_tokens=16384, max_retries=5):
    """Call a Qwen model via an OpenAI-compatible API endpoint (using requests).

    Works with:
      - Ollama (default)
      - Local vLLM / SGLang servers
      - Together AI, Fireworks, Alibaba DashScope, etc.
    """
    url = f"{QWEN_API_BASE}/chat/completions"
    headers = {
        "Content-Type": "application/json",
        "Authorization": f"Bearer {QWEN_API_KEY}",
    }
    payload = {
        "model": model,
        "messages": messages,
        "temperature": temperature,
        "max_tokens": max_tokens,
    }

    for attempt in range(max_retries):
        try:
            resp = requests.post(url, headers=headers, json=payload, timeout=600)
            resp.raise_for_status()
            data = resp.json()
            content = data["choices"][0]["message"]["content"]
            if content:
                return content.strip()
            # Qwen3 thinking mode: content may be empty if all tokens went to reasoning
            reasoning = data["choices"][0]["message"].get("reasoning", "")
            if reasoning:
                print(f"[Attempt {attempt + 1}] Model returned reasoning only, no content. Retrying...")
            else:
                return ""

        except Exception as e:
            print(f"[Attempt {attempt + 1}] Error calling Qwen model: {e}")

        sleep_time = 2 ** attempt  # Exponential backoff
        print(f"Retrying in {sleep_time} seconds...")
        time.sleep(sleep_time)

    raise RuntimeError(f"call_qwen failed after {max_retries} retries.")


def qwen_response(messages, model_name):
    """Thin wrapper matching the gpt_response() signature."""
    return call_qwen(model=model_name, messages=messages)


def setup_logging(output_file):
    # Create log file name by replacing .txt with .log
    log_file = output_file.replace('.txt', '.log')

    # Create a file to capture all console output
    log_file_handle = open(log_file, 'w')

    # Create a stream that writes to both console and file
    class Tee(io.TextIOBase):
        def __init__(self, file1, file2):
            self.file1 = file1
            self.file2 = file2

        def write(self, data):
            self.file1.write(data)
            self.file2.write(data)
            self.file2.flush()

        def flush(self):
            self.file1.flush()
            self.file2.flush()

    # Redirect both stdout and stderr to our Tee stream
    sys.stdout = Tee(sys.stdout, log_file_handle)
    sys.stderr = Tee(sys.stderr, log_file_handle)

    return log_file_handle


def find_relevant_theorems(args, theorems, problems_set):
    relevant_theorems = {}
    for key in theorems.keys():
        for problem in problems_set:
            if args.variant == "random_no_theorems":
                continue
            if args.variant == "analogy_based" and problem in key:
                relevant_theorems[key] = theorems[key]
            if args.variant in ["random_all_theorems", "analogy_based_all_theorems"]:
                relevant_theorems[key] = theorems[key]
    return relevant_theorems


def get_problem_fields(problem):
    construction_cdl = "\n".join(problem.construction_cdl)
    text_cdl = "\n".join(problem.text_cdl)
    construction_cdl_extended = "\n".join(problem.construction_cdl_extended)
    theorem_seqs = "\n".join(f"{i + 1};{problem.theorem_seqs[i]}" for i in range(len(problem.theorem_seqs)))
    equations = "\n".join(problem.equations)
    return {'construction_cdl': construction_cdl, 'text_cdl': text_cdl,
            'construction_cdl_extended': construction_cdl_extended, 'theorem_seqs': theorem_seqs,
            'equations': equations}


def convert_json_list_to_custom_format(json_list):
    result = []

    for index, item in enumerate(json_list, start=1):
        # Parse the JSON string into a dictionary
        theorem_dict = json.loads(item)

        # Extract the fields
        theorem = theorem_dict.get("theorem", "")
        premise = theorem_dict.get("premise", "")
        conclusion = theorem_dict.get("conclusion", [])

        # Format the conclusion as a string
        conclusion_str = json.dumps(conclusion)

        # Create the custom formatted string
        formatted_string = f"step_id: {index}; theorem: {theorem}; premise: {premise}; conclusion: {conclusion_str}"

        # Append to the result list
        result.append(formatted_string)

    # Join all the formatted strings into a single string with line breaks
    return "\n".join(result)


def get_processed_model_resp(resp):
    generated_theorem_sequence = resp.split("THEOREM_SEQUENCE:\n")[1] if len(
        resp.split("THEOREM_SEQUENCE:\n")) > 1 else ""
    generated_theorem_sequence = convert_theorem_seqs_format_string(
        generated_theorem_sequence) if generated_theorem_sequence != "" else ""
    generated_theorem_sequence_list = [line.split(";")[1].strip() for line in generated_theorem_sequence.strip().split(
        "\n")] if generated_theorem_sequence != "" else []
    return generated_theorem_sequence_list


def convert_theorem_seqs_format_string(input_str):
    # Remove leading and trailing single quotes if present
    input_str = input_str.strip("'")

    # Split the input string by lines
    lines = input_str.strip().splitlines()

    converted_list = []

    for line in lines:
        line = line.strip()
        if line.startswith("step_id:"):
            # Split the line by ';' and extract labeled parts
            parts = [part.split(":", 1)[1].strip() for part in line.split(";") if ":" in part]
        else:
            # Assume the line is unlabeled and split by ';'
            parts = [part.strip() for part in line.split(";")]

        step_id = parts[0] if len(parts) > 0 else ""
        theorem = parts[1] if len(parts) > 1 else ""
        premise = parts[2] if len(parts) > 2 else ""
        conclusion = parts[3] if len(parts) > 3 else ""

        converted_list.append(f"{step_id};{theorem};{premise};{conclusion}")

    return "\n".join(converted_list)


def create_messages(content):
    # Constructing the initial message with the user role
    initial_message = {"role": "user", "content": content}

    # Only include the user message
    messages = [initial_message]

    return messages


def get_theorems_from_similar_problems(similar_problems):
    relevant_theorems = set()
    for problem in similar_problems:
        for theorem in problem.abstract_theorem_seqs:
            relevant_theorems.add(theorem)
    return relevant_theorems


def get_theorems_problem_to_solve(problem):
    relevant_theorems = set()
    for theorem in problem.abstract_theorem_seqs:
        relevant_theorems.add(theorem)
    return relevant_theorems


def get_prompt_template_content(args, gdl_relevant_theorems, similar_problems, problem2):
    with open(args.prompt_path, 'r') as file:
        initial_prompt = file.read()
    gdl_relevant_theorems_str = json.dumps(gdl_relevant_theorems, indent=4)
    initial_prompt = initial_prompt.replace('{GDL}', gdl_relevant_theorems_str)
    content = initial_prompt

    for i in range(IN_CONTEXT_FEW_SHOT):
        problem = similar_problems[i]
        problem_dict = get_problem_fields(problem)
        theorems_seqs_expl = convert_json_list_to_custom_format(get_theorem_seqs_expl(problem.theorem_seqs))
        content += f"\nInputs for Problem A{i + 1}:\nDESCRIPTION:\n{problem.description}\nCONSTRUCTION_CDL:\n{problem_dict['construction_cdl']}\n"
        content += f"TEXT_CDL:\n{problem_dict['text_cdl']}\nGOAL_CDL:\n{problem.goal_cdl}\nCONSTRUCTION_CDL_EXTENDED:\n{problem_dict['construction_cdl_extended']}\nSYMBOLS_AND_VALUES:\n{problem.symbols_and_values}\n"
        content += f"Outputs:\nOutputs for Problem A{i + 1}:\nEQUATIONS:\n{problem_dict['equations']}\nGOAL_SYMBOL:\n{problem.goal_symbol}\nANSWER:\n{problem.answer}\nTHEOREM_SEQUENCE:\n{theorems_seqs_expl}\n"

    problem_dict = get_problem_fields(problem2)
    content += f"Inputs for Problem B:\nDESCRIPTION:\n{problem2.description}\n"
    content += f"CONSTRUCTION_CDL:\n{problem_dict['construction_cdl']}\nTEXT_CDL:\n{problem_dict['text_cdl']}\nGOAL_CDL:\n{problem2.goal_cdl}\n"
    content += f"CONSTRUCTION_CDL_EXTENDED:\n{problem_dict['construction_cdl_extended']}\nSYMBOLS_AND_VALUES:\n{problem.symbols_and_values}\nOutputs:\nOutputs for Problem B:\n"
    return content


def add_model_answer_to_feedback(feedback, resp):
    model_response = ""
    if "ANSWER:" in resp:
        answer_section = resp.split("ANSWER:")[1]
        answer_part = answer_section.split("THEOREM_SEQUENCE:")[0].strip()
        model_response = f"RETRY_ANSWER:\n{answer_part}\nRETRY_THEOREM_SEQUENCE:\n{answer_section.split('THEOREM_SEQUENCE:')[1].strip()}"
    return f"{feedback}\nModel Answer:\n{model_response}"


def generate_and_verify(args, gdl_relevant_theorems, similar_problems, problem2, run_id):
    content = get_prompt_template_content(args, gdl_relevant_theorems, similar_problems, problem2)
    messages = create_messages(content)
    start_index = messages[0]['content'].find("Inputs for Problem B:")
    problem2_given = messages[0]['content'][start_index:]
    problem2_gt = get_gt_result(problem2)
    file_path = f"results/level_{problem2.level}/variant_{args.variant}_model_{args.model_name}_problem_{problem2.id}_run_{run_id}_to_verify.txt"
    attempts = 0
    verifier_result = ""
    resp = ""
    retries_messages = []

    total_t0 = time.perf_counter()
    attempt_durations = []

    while attempts < MAX_RETRIES_IN_RUN:
        t0 = time.perf_counter()
        resp = qwen_response(messages, args.model_name)
        write_result(file_path, problem2_given, resp, problem2_gt, retries_messages, run_id)

        verifier = Verifier(problem2.id, resp)
        verify_symbols_syntax_result = verifier.verify_symbols_syntax()
        verify_geometric_proof_result, feedback, error_tier = verify_geometric_proof(file_path, print_output=False)
        attempt_durations.append(time.perf_counter() - t0)

        error_tier = error_tier.name if error_tier else error_tier
        if verify_symbols_syntax_result == "Success" and not feedback:
            verifier_result = verify_symbols_syntax_result
            print("Theorem sequence verified correctly")
            break
        else:
            messages.append({"role": "assistant", "content": resp})
            if verify_symbols_syntax_result != "Success":
                verifier_result = add_model_answer_to_feedback(verify_symbols_syntax_result, resp)
                error_tier = "TIER1_THEOREM_CALL_SYNTAX_VIOLATION"
            else:
                verifier_result = add_model_answer_to_feedback(feedback, resp)
            verifier_result = "ERROR_TIER: " + error_tier + "\n" + verifier_result
            messages.append({"role": "user", "content": f"Verifier result: {verifier_result}"})
            print(f"Verifier result: {verifier_result}")
            attempts += 1
            print(f"Retry attempt: {attempts}")
            retries_messages.append(verifier_result)

    total_elapsed = time.perf_counter() - total_t0
    print(f"Total time: {total_elapsed:.3f}s | per attempt: {[round(x,3) for x in attempt_durations]}")

    # (Optional) persist timings next to the result
    try:
        with open(file_path.replace(".txt", "_timing.txt"), "a") as f:
            f.write(f"Total: {total_elapsed:.6f}s\n")
            for i, dt in enumerate(attempt_durations, 1):
                f.write(f"Attempt {i}: {dt:.6f}s\n")
    except Exception:
        pass

    return messages, resp, verifier_result, retries_messages


def get_level_to_problems(problems):
    level_to_problems = {}
    for problem_id, problem_obj in problems.items():
        level = problem_obj.level
        if level not in level_to_problems:
            level_to_problems[level] = [problem_id]
        else:
            level_to_problems[level].append(problem_id)
    return level_to_problems



import matplotlib.pyplot as plt
import collections
import random


def plot_true_count_by_level(true_count_by_level):
    x_values = list(true_count_by_level.keys())
    y_values = list(true_count_by_level.values())
    plt.figure(figsize=(8, 6))
    plt.bar(x_values, y_values, width=0.6, color='blue', edgecolor='black')
    plt.xlim(0, 9)
    plt.ylim(0, 10)
    plt.xlabel('Keys (0 to 9)')
    plt.ylabel('Values (0 to 10)')
    plt.title('Histogram of defaultdict')
    plt.show()


def print_similar_problems_theorems_coverage(variant, chosen_problems_by_level):
    problem_id_to_level = {}
    for level, problems in chosen_problems_by_level.items():
        for problem_id in problems:
            problem_id_to_level[problem_id] = level

    true_count_by_level = collections.defaultdict(int)
    file_name = f'cover_theorems_{variant}_{SIMILAR_PROBLEMS}_levels_{MIN_LEVEL}_{MAX_LEVEL}.csv'

    df = pd.read_csv(file_name)
    df['IsCovered'] = df['IsCovered'].astype(str) == 'True'
    df['LevelID'] = df['ProblemID'].map(problem_id_to_level)
    df.to_csv(file_name, index=False)
    covered_df = df[df['IsCovered']]
    for _, row in covered_df.iterrows():
        level = row['LevelID']
        if pd.notna(level):
            true_count_by_level[level] += 1

    total = 0
    for level, count in true_count_by_level.items():
        total += count

    print("count problems: ", len(problem_id_to_level))
    print("count covered problems: ", total)
    print("coverage %:", total / len(problem_id_to_level))
    print(true_count_by_level)

    avg_problem_to_solve = df['ProblemToSolveTheorems'].mean()
    avg_similar_problems = df['SimilarProblemsTheorems'].mean()

    print(f"Average ProblemToSolveTheorems: {avg_problem_to_solve:.2f}")
    print(f"Average SimilarProblemsTheorems: {avg_similar_problems:.2f}")


def get_chosen_problems_by_level(problems, seed):
    random.seed(seed)
    level_to_problems = get_level_to_problems(problems)
    chosen_problems_by_level = {}

    for level, problem_ids in level_to_problems.items():
        if 1 <= level <= 10:
            sample_problem_ids = random.sample(problem_ids, 10)
            chosen_problems_by_level[level] = sample_problem_ids

    # --- Now sample 10 more problems for each level without duplicates ---
    for level, problem_ids in level_to_problems.items():
        if 1 <= level <= 10:
            already_sampled = set(chosen_problems_by_level[level])
            available_problem_ids = list(set(problem_ids) - already_sampled)
            if len(available_problem_ids) < 10:
                raise ValueError(f"Not enough problems to sample 10 more in level {level}")
            more_sampled = random.sample(available_problem_ids, 12)
            # Add the new samples
            chosen_problems_by_level[level].extend(more_sampled)

    return chosen_problems_by_level


def write_theorems_coverage_stats(similar_problems_theorems, problem2, variant, num_examples):
    problem_to_solve_theorems = get_theorems_problem_to_solve(problem2)
    all_present = problem_to_solve_theorems.issubset(similar_problems_theorems)
    file_name = f'cover_theorems_{variant}_{num_examples}_levels_{MIN_LEVEL}_{MAX_LEVEL}.csv'
    new_data = pd.DataFrame(
        [[problem2.id, all_present, len(problem_to_solve_theorems), len(similar_problems_theorems)]],
        columns=['ProblemID', 'IsCovered', 'ProblemToSolveTheorems', 'SimilarProblemsTheorems'])
    if os.path.exists(file_name):
        existing_data = pd.read_csv(file_name)
        updated_data = pd.concat([existing_data, new_data], ignore_index=True)
    else:
        updated_data = new_data
    updated_data.to_csv(file_name, index=False)


def get_gt_result(problem2):
    gt = ""
    gt += "\n\nGT_EQUATIONS:\n" + "\n".join(problem2.equations) + "\n"
    gt += "GT_GOAL_SYMBOL:\n" + problem2.goal_symbol + "\n"
    gt += "GT_ANSWER:\n" + problem2.answer + "\n"
    theorems_seqs_expl = convert_json_list_to_custom_format(get_theorem_seqs_expl(problem2.theorem_seqs))
    theorem_seqs_format = convert_theorem_seqs_format_string(theorems_seqs_expl)
    gt += "GT_THEOREM_SEQUENCE:\n" + theorem_seqs_format + "\n"
    return gt


def write_result(file_path, problem2_given, problem2_resp, problem2_gt, retries_messages, run_id):
    with open(file_path, "w") as file:
        file.write(problem2_given + "\n")
        file.write("***MODEL_RESPONSE_BEGIN***" + "\n")
        file.write(problem2_resp + "\n")
        file.write("***MODEL_RESPONSE_END***" + "\n")
        file.write("RETRIES_MESSAGES:\n")
        for i, message in enumerate(retries_messages):
            file.write("#run: " + str(run_id) + "; #retry: " + str(i + 1) + '; message: ' + message + "\n")
        file.write("#RETRIES:\n")
        file.write(str(len(retries_messages)) + "\n")
        file.write("#RUNS:\n")
        file.write(str(run_id) + "\n")
        file.write(problem2_gt + "\n")
    print(f"Content written to {file_path}")


def process_problem(problem_id, solver=None, problems=None):
    problem = problems[problem_id]
    problem.print_problem()
    problem.enrich_problem()
    problem_CDL = dl.get_problem(problem_id)
    solver.load_problem(problem_CDL)
    # display_image(problem_id)
    return problem


def run(args, problem2_id, problems, run_id):
    if args.variant in ["analogy_based", "analogy_based_all_theorems"]:
        similar_problem_ids = retrieve_similar_proofs(problem2_id, n=SIMILAR_PROBLEMS)
    else:
        similar_problem_ids = retrieve_random_proofs(problem2_id, n=SIMILAR_PROBLEMS)
    similar_problems = [process_problem(problem_id, solver, problems) for problem_id in similar_problem_ids]
    problem2 = process_problem(problem2_id, solver, problems)
    similar_problems_theorems = get_theorems_from_similar_problems(similar_problems)
    gdl_relevant_theorems = find_relevant_theorems(args, theorems, similar_problems_theorems)
    write_theorems_coverage_stats(similar_problems_theorems, problem2, args.variant, 20)

    # Set up logging for this run
    output_path = f"results/level_{problem2.level}/variant_{args.variant}_model_{args.model_name}_problem_{problem2.id}_run_{run_id}.txt"
    log_file_handle = setup_logging(output_path)

    try:
        messages, problem2_resp, verifier_result, retries_messages = generate_and_verify(args,
                                                                                         gdl_relevant_theorems,
                                                                                         similar_problems, problem2,
                                                                                         run_id)
        problem2_gt = get_gt_result(problem2)
        start_index = messages[0]['content'].find("Inputs for Problem B:")
        problem2_given = messages[0]['content'][start_index:]

        # Write the original output file
        write_result(output_path, problem2_given, problem2_resp, problem2_gt, retries_messages, run_id)

        return len(retries_messages) < MAX_RETRIES_IN_RUN
    except Exception as e:
        # Print the full traceback to the log file
        import traceback
        traceback.print_exc(file=sys.stderr)
        raise  # Re-raise the exception after logging it
    finally:
        # Close the log file handle
        log_file_handle.close()
        # Restore stdout and stderr
        sys.stdout = sys.__stdout__
        sys.stderr = sys.__stderr__


def run_theorems_coverage(args, run=True, print_results=True):
    random.seed(1234)
    level_to_problems = get_level_to_problems(problems)
    chosen_problems_by_level = {}
    for level, problem_ids in level_to_problems.items():
        if MIN_LEVEL <= level <= MAX_LEVEL:
            sample_problem_ids = random.sample(problem_ids, SAMPLED_PROBLEMS_IN_LEVEL)
            chosen_problems_by_level[level] = sample_problem_ids
    if run:
        for _, problems_id in chosen_problems_by_level.items():
            for problem2_id in problems_id:
                if args.variant in ["analogy_based", "analogy_based_all_theorems"]:
                    similar_problem_ids = retrieve_similar_proofs(problem2_id, n=SIMILAR_PROBLEMS)
                else:
                    similar_problem_ids = retrieve_random_proofs(problem2_id, n=SIMILAR_PROBLEMS)
                print("Probles retrieved: ", similar_problem_ids)
                similar_problems = [process_problem(problem_id, solver, problems) for problem_id in similar_problem_ids]
                problem2 = process_problem(problem2_id, solver, problems)
                similar_problems_theorems = get_theorems_from_similar_problems(similar_problems)
                write_theorems_coverage_stats(similar_problems_theorems, problem2, args.variant, SIMILAR_PROBLEMS)
    if print_results:
        print_similar_problems_theorems_coverage(args.variant, chosen_problems_by_level)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--variant", dest="variant", type=str, default="analogy_based")
    parser.add_argument("--model_name", dest="model_name", type=str, default="qwen3:8b")
    parser.add_argument("--api_base", dest="api_base", type=str, default=None,
                        help="OpenAI-compatible API base URL (overrides QWEN_API_BASE env var)")
    parser.add_argument("--api_key", dest="api_key", type=str, default=None,
                        help="API key (overrides QWEN_API_KEY env var)")
    parser.add_argument("--prompt_path", dest="prompt_path", type=str,
                        default="src/formalgeo/prompt/geometry_similar_problems_prompt.txt")
    args = parser.parse_args()

    # Allow CLI args to override the endpoint
    if args.api_base:
        QWEN_API_BASE = args.api_base
    if args.api_key:
        QWEN_API_KEY = args.api_key

    problems = save_problems(os.path.join(PROJECT_ROOT, 'formalgeo7k_v1/problems'))
    run_solver = True
    # chosen_problems_by_level = get_chosen_problems_by_level(problems, seed=42)
    if run_solver:
        try:
            for _, problems_id in chosen_problems_by_level.items():
                for problem2_id in problems_id:
                    for i in range(MAX_RUNS):
                        is_success = run(args, problem2_id, problems, i)
                        if is_success:
                            break
        except Exception as e:
            traceback.print_exc(file=sys.stderr)
            raise
    # run_theorems_coverage(args, run=False, print_results=False)
