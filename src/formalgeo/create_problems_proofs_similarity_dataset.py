import os
import json
import csv
import re

import pandas as pd

from Problem import Problem
from collections import Counter
import argparse
import collections
import matplotlib
matplotlib.use('TkAgg')
import matplotlib.pyplot as plt


def remove_duplicates(theorem_seqs):
    seen = set()
    unique_res = []
    for seq in theorem_seqs:
        if seq not in seen:
            unique_res.append(seq)
            seen.add(seq)
    return unique_res
def get_abstract_theorem_seqs(theorem_seqs):
    res = []
    for seq in theorem_seqs:
        res.append(seq.split("(")[0])
    return remove_duplicates(res)

def get_abstract_theorem_seq_dag(theorem_seqs_dag):
    new_data = {}
    for key, value_list in theorem_seqs_dag.items():
        new_key = key.split('(')[0].strip()
        new_value_list = [value.split('(')[0].strip() for value in value_list]
        new_data[new_key] = new_value_list
    return new_data


def replace_letters_and_numbers(text):
    text = re.sub(r'\d+', '<num>', text)
    def replace_letters(match):
        return re.sub(r'\b[A-Z]+\b', '<word>', match.group(0))

    return re.sub(r'\([^\(\)]+\)', replace_letters, text)

def print_problem_level_dist(problems):
    level_count = collections.defaultdict(int)
    for problem in problems.values():
        level_count[problem.level] += 1

    for level, count in level_count.items():
        print(f"Level {level}: {count} problems")

    # levels = list(level_count.keys())
    # counts = list(level_count.values())
    # plt.bar(levels, counts)
    # plt.xlabel('Level')
    # plt.ylabel('Number of Problems')
    # plt.title('Problem Level Distribution')
    # plt.xticks(levels)  # Ensure each level has its own tick
    # plt.show()


def print_problem(json, verbose=False):
    text_cdl = json['text_cdl']
    construction_cdl = json['construction_cdl']
    goal_cdl = json['goal_cdl']

    abstract_text_cdl = [replace_letters_and_numbers(s) for s in text_cdl]
    abstract_construction_cdl = [replace_letters_and_numbers(s) for s in construction_cdl]
    abstract_goal_cdl = replace_letters_and_numbers(goal_cdl)

    abstract_theorem_seqs = get_abstract_theorem_seqs(json['theorem_seqs'])
    abstract_theorem_seq_dag = get_abstract_theorem_seq_dag(json['theorem_seqs_dag'])

    if verbose:
        print("problem id: {}".format(json['problem_id']))
        print("problem level: {}".format(json['problem_level']))
        print("problem description: {}".format(json['problem_text_en']))
        print("construction_cdl")
        print(construction_cdl)
        print("abstract_construction_cdl")
        print(abstract_construction_cdl)
        print("text_cdl")
        print(text_cdl)
        print("abstract text_cdl")
        print(abstract_text_cdl)
        print("problem goal: {}".format(goal_cdl))
        print("abstract problem goal: {}".format(abstract_goal_cdl))
        print("problem answer: {}".format(json['problem_answer']))
        print("problem theorem seqs: {}".format(json['theorem_seqs']))
        print("problem abstract theorem seqs: {}".format(abstract_theorem_seqs))
        print("problem abstract theorem seqs dag: {}".format(json['theorem_seqs_dag']))
        print("problem abstract theorem seqs dag: {}".format(abstract_theorem_seq_dag))

    return Problem(json['problem_id'], json['problem_level'], json['problem_text_en'], json['problem_answer'], construction_cdl,
                   abstract_construction_cdl, text_cdl, abstract_text_cdl, goal_cdl, abstract_goal_cdl,
                   json['theorem_seqs'], abstract_theorem_seqs, json['theorem_seqs_dag'], abstract_theorem_seq_dag)


def save_problems(directory_path):
    count = 0
    problems = {}
    for filename in os.listdir(directory_path):
        count += 1
        if filename.endswith('.json'):
            file_path = os.path.join(directory_path, filename)
            with open(file_path, 'r') as file:
                json_data = json.load(file)
                problem = print_problem(json_data)
                problems[problem.id] = problem
    print_problem_level_dist(problems)
    return problems


def write_problems_proofs_similarity_dataset(output_file = 'problems_similarity_results.csv'):
    keys = list(problems.keys())
    count = 0
    results = []
    column_names = ["problem1_id", "problem1_level", "problem2_id", "problem2_level", "abstract_construction_cdl_jaccard_similarity",
                    "abstract_text_cdl_jaccard_similarity", "abstract_goal_similarity", "abstract_theorem_seqs_jaccard_similarity"]
    n = len(keys)
    num_iterations = n * (n - 1) // 2
    for i in range(n):
        for j in range(i + 1, n):
            count += 1
            print("Iteration: " + str(count))
            print("Progress %: " + str(count / num_iterations * 100))
            problem1_id, problem2_id = keys[i], keys[j]
            problem1_level, problem2_level = problems[problem1_id].level, problems[problem2_id].level
            problem1_abstract_construction_cdl, problem2_abstract_construction_cdl = problems[
                problem1_id].abstract_construction_cdl, problems[problem2_id].abstract_construction_cdl
            problem1_abstract_text_cdl, problem2_abstract_text_cdl = problems[problem1_id].abstract_text_cdl, problems[
                problem2_id].abstract_text_cdl
            problem1_abstract_goal_cdl, problem2_abstract_goal_cdl = problems[problem1_id].abstract_goal_cdl, problems[
                problem2_id].abstract_goal_cdl
            problem1_abstract_theorem_seqs, problem2_abstract_theorem_seqs = (
                problems[problem1_id].abstract_theorem_seqs, problems[problem2_id].abstract_theorem_seqs)


            abstract_construction_cdl_jaccard_similarity = calc_Jaccard_sim_between_multisets(
                problem1_abstract_construction_cdl, problem2_abstract_construction_cdl)
            # print("problems construction jaccard similarity: " + str(abstract_construction_cdl_jaccard_similarity))

            abstract_text_cdl_jaccard_similarity = calc_Jaccard_sim_between_multisets(problem1_abstract_text_cdl,
                                                                                      problem2_abstract_text_cdl)
            # print("problems text jaccard similarity: " + str(abstract_text_cdl_jaccard_similarity))

            abstract_goal_similarity = 1.0 if problem1_abstract_goal_cdl == problem2_abstract_goal_cdl else 0.0
            # print("problems goal similarity: " + str(abstract_goal_similarity))

            abstract_theorem_seqs_jaccard_similarity = calc_Jaccard_sim_between_multisets(problem1_abstract_theorem_seqs, problem2_abstract_theorem_seqs)
            # print("problems abstract theorem seqs jaccard similarity: " + str(abstract_theorem_seqs_jaccard_similarity))

            results.append([problem1_id, problem1_level, problem2_id, problem2_level, abstract_construction_cdl_jaccard_similarity,
                            abstract_text_cdl_jaccard_similarity, abstract_goal_similarity,
                            abstract_theorem_seqs_jaccard_similarity])

            print()

    with open(output_file, mode='w', newline='') as file:
        writer = csv.writer(file)
        writer.writerow(column_names)
        writer.writerows(results)
    print("Data has been saved to " + output_file)

def calc_Jaccard_sim_between_multisets(l1, l2):
    multiset1 = Counter(l1)
    multiset2 = Counter(l2)

    intersection = sum((multiset1 & multiset2).values())
    union = sum((multiset1 | multiset2).values())

    if union == 0:
        return 0
    return intersection / union


def main():
    parser = argparse.ArgumentParser(description='Control dataset generation.')
    parser.add_argument('--run-generate-dataset', action='store_true',
                        help='Flag to run the dataset generation')

    args = parser.parse_args()
    args.run_generate_dataset = True
    output_file = 'problems_similarity_results.csv'
    if args.run_generate_dataset:
        write_problems_proofs_similarity_dataset(output_file = output_file)

    df = pd.read_csv(output_file)
    result = df.groupby('problem1_id')['problem2_id'].nunique().reset_index()
    result.columns = ['problem1_id', 'num_unique_problem2']


if __name__ == "__main__":
    problems = save_problems('formalgeo7k_v1/problems')
    main()
