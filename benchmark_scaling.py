#!/usr/bin/env python3

import subprocess
import sys, os
from os.path import abspath
from pathlib import Path
from typing import Tuple, List
import re
from enum import Enum
from collections import defaultdict
from functools import reduce

servois2_dir = './'
yml_dir = './yamls/generate_yaml/'

servois2 = servois2_dir + 'src/servois2'

TIMEOUT = 120

N_TRIALS = 1

N_MAX_VARS = 20

# TODO: speedup of poke2-lattice over poke? poke2 over poke?

class Heuristic(Enum):
    SIMPLE = 0
    POKE = 11
    POKE2 = 21
    MC_MAX = 31
    
    def __str__(self):
        return string_of_heuristic[self]

string_of_heuristic = {
    Heuristic.SIMPLE: "simple",
    Heuristic.POKE: "poke",
    Heuristic.POKE2: "poke2",
    Heuristic.MC_MAX: "mc-max"
}

command_of_heuristic = {
    Heuristic.SIMPLE: [],
    Heuristic.POKE: ["--poke"],
    Heuristic.POKE2: ["--poke2"],
    Heuristic.MC_MAX: ["--mcpeak-max"],
}    

benches_type = defaultdict(lambda: str, {
    'predicates': int,
    'predicates_filtered': int,
    'smtqueries': int,
    'mcqueries': int,
    'time_lattice_construct': float,
    'time_mc_run': float,
    'time_synth': float,
    'time': float
})

class TestCase():
    def __init__(self, heuristic, opts = ()):
        self.heuristic = heuristic
        self.opts = opts
        self.ran = False
    def run(self, yml, m, n):
        command_infer = [
            servois2, 'synth', '-q',
            '--timeout', str(TIMEOUT), '--prover', 'cvc4'
        ] + list(map(str, self.opts)) + command_of_heuristic[self.heuristic] + [yml_dir + yml, m, n]
        sys.stdout.write(f'Running command: {str(command_infer)}\n')
        try:
            benches = defaultdict(float) # Doesn't only contain floats, but only will blindly query for them.
            for x in range(N_TRIALS):
                stdout, stderr = run_command(command_infer)
                result, benches_trial = process_output(stdout, stderr)
                for bench in benches_trial:
                    res = benches_type[bench](benches_trial[bench])
                    if benches_type[bench] is float:
                        benches[bench] += res
                    elif bench not in benches:
                        benches[bench] = res
            if not "time" in benches: raise Exception(stdout, stderr)
            benches = { k: v/N_TRIALS if benches_type[k] is float else v for (k, v) in benches.items() }
        except Exception as err:
            result = "false"
            benches = None
            sys.stdout.write(f'\nFailure: {str(err.args)}\n')

        sys.stdout.write(f'Done.\n')
        sys.stdout.flush()

        self.res = result
        self.benches = benches
        self.ran = True
    def __str__(self):
        return str((str(self.heuristic),) + tuple(map(str, self.opts)))

def make_scale_heuristics(test_dict): # -> dict[str, dict[tuple[str, str], list[TestCase]]]:
    return {
        yml: {
            (ms[0], ms[1]): [TestCase(h, ms[2:]) for h in string_of_heuristic]
            for ms in test_dict[yml]
            }
        for yml in test_dict
        }

name_of_yml = {
    ('lia_{}vars.yaml'.format(i+1)): 'LIA 2+{} vars'.format(i+1) 
    for i in range(N_MAX_VARS)
}

table3_heuristics = [Heuristic.POKE, Heuristic.POKE2]

testcases = {
    # First, the cases that are to be run on /all/ heuristics (LIA and String)
    ** make_scale_heuristics({
        ('lia_{}vars.yaml'.format(i+1)): [('sum', 'multiVarCondSum')] 
        for i in range(N_MAX_VARS)
    })
}

def process_output(stdout, stderr):
    try:
        res = latex_of_phi(stdout)
        benches = dict(line.split(', ') for line in stderr.strip().split('\n'))
    except:
        raise Exception(stdout, stderr)
    return res, benches

# LaTeX utilities:
NA_STRING = '--'

def latex_tt(s : str) -> str:
    return f'\\texttt{{{s}}}'

def latex_of_time(t : float):
    return f'{t:#.2f}'

op_map = {
    '==': '!=',  '!=': '==',
    '<': '>=',   '>=': '<',
    '>': '<=',   '<=': '>'
}
op_map_escaped = {
    re.escape(k): re.escape(v) 
    for k,v in op_map.items()
}

re_ops = '|'.join(map(re.escape, op_map_escaped.keys()))
re_term = r'.*?'

re_neg_match = re.compile(
    fr''' ! \s? \( 
        \s? (?P<arg1>{re_term}) \s? 
        (?P<op>{re_ops}) \s? 
        (?P<arg2>{re_term}) \s? \) 
        ''',
    re.X
)

def re_neg_goal(r : re.Match) -> str:
    arg1 = r.group('arg1')
    op   = r.group('op')
    arg2 = r.group('arg2')
    res = f'{arg1} {op_map[op]} {arg2}'
    return res

# https://texblog.net/latex-archive/uncategorized/symbols/
def latex_escape(s : str):
    s = s.replace('#', '\\#')
    s = s.replace('$', '\\$')
    s = s.replace('%', '\\%')
    s = s.replace('_', '\\_')
    s = s.replace('&', '\\&')
    s = s.replace('{', '\\{')
    s = s.replace('}', '\\}')
    s = s.replace('^', '\\^{}')
    s = s.replace('||', '\\textbar\\textbar\\ ')
    s = s.replace('> ', '\\textgreater\\ ')
    s = s.replace('< ', '\\textless\\ ')
    return s

## Replaces '!(_ op _)' with '_ !op _'
def latex_of_exp(exp : str, abridge=False) -> str:
    exp = re.sub(re_neg_match, re_neg_goal, exp)
    if abridge:
        l = exp.split('||')
        if len(l) > 2:
            exp = f'{l[0]}|| ... ||{l[-1]}'
    return exp

def latex_of_phi(phi, abridge=False) -> str:
    if not phi:
        return NA_STRING
    p = latex_of_exp(phi, abridge)
    p = latex_escape(p)
    p = latex_tt(p)
    return p

def string_of_ms(ms):
    if len(ms) > 2:
        if ms[2] is AdditionalOptions.LEFT_MOVER:
            return ms[1] + ' $ \\rrrm $ ' + ms[0]
        else:
            return ms[0] + ' $ \\rrrm $ ' + ms[1]
    else:
        return ms[0] + ' $ \\bowtie $ ' + ms[1]

mkheader = lambda cols : (
    "\\begin{table} \\begin{center} \\begin{tabular}{|l|c|c|" + '|'.join(["r" for _ in cols]) + "|} \\hline\n" +
    "\\bf{ADT} & \\bf{Methods} & \\bf{NPreds} & " + ' & '.join(f'\\bf{{{str(h)}}}' for h in cols) + "\\\\\n"
)

table3_header = mkheader(table3_heuristics)

table3_footer = (
    "\\hline\n"+
    "\\end{tabular}\n" +
    "\\end{center}\n" +
    "\\caption{\\label{table:one}Total execution time comparison between \\poke{} and new heuristics when scaling the number of variables/predicates (Timout set to 60s). Speedup relative to \\poke{} is given in parentheses. All times are given in seconds.}\n" +
    "\\end{table}\n"
)

def find_result(yml, ms, reslist, heuristic):
    for t in reslist:
        if t.heuristic is heuristic:
            if not t.ran: t.run(yml, ms[0], ms[1]) # Run test cases lazily
            return t.benches
    else:
        return None

prod = lambda l: reduce(lambda x, y: x * y, l, 1)
geomean = lambda l: prod(l) ** (1 / len(l)) if l else 1

def make_table3(cases):
    table = table3_header
    # Speedup relative to poke
    poke2_speedup = []
    mc_max_speedup = []
    predicates_size = 0
    for yml in cases:
        section = "\\hline\n" + name_of_yml[yml]
        for ms in cases[yml]:
            results = cases[yml][ms]
            row_heurs = defaultdict(lambda: None)
            for heur in table3_heuristics:
                try:
                    row_heurs[heur] = find_result(yml, ms, results, heur)["time"]
                except:
                    pass
            poke2_speedup.append(row_heurs[Heuristic.POKE] / row_heurs[Heuristic.POKE2])
            if Heuristic.MC_MAX in row_heurs:
                mc_max_speedup.append(row_heurs[Heuristic.POKE] / row_heurs[Heuristic.MC_MAX])
            predicates_size = find_result(yml, ms, results, Heuristic.POKE2)["predicates_filtered"]
            def str_of_heur(h):
                try:
                    if h is min(row_heurs, key=row_heurs.get):
                        if h is Heuristic.POKE: return "\\bf{{{:.2f}}}".format(row_heurs[h])
                        else: return "\\bf{{{:.2f}}}({:.1f}$\\times$)".format(row_heurs[h], row_heurs[Heuristic.POKE] / row_heurs[h])
                    else:
                        if h is Heuristic.POKE: return "{:.2f}".format(row_heurs[h])
                        else: return "{:.2f}({:.1f}$\\times$)".format(row_heurs[h], row_heurs[Heuristic.POKE] / row_heurs[h])
                except: return NA_STRING
            section += f' & {string_of_ms(ms)} ' + f' & {predicates_size} & ' + ' & '.join([str_of_heur(h) for h in table3_heuristics]) + "\\\\\n"
        table += section
    table += table3_footer
    # TODO: We're taking the geomean across potentially the arithmetic mean of individual trials. Invalid?
    table += (
        "\\newcommand{{\\poketwospeedup}}{{{:.2f}}}\n".format(geomean(poke2_speedup)) + 
        "\\newcommand{{\\mcmaxspeedup}}{{{:.2f}}}\n".format(geomean(mc_max_speedup))
    )
    return table


def run_command(command : List[str]):
    popen = subprocess.Popen(
        command, universal_newlines=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )
    out, err = popen.communicate()
    if 'error' in err or 'exception' in err:
        raise Exception(err)
    return out, err

if __name__ == '__main__':
    if len(sys.argv) > 1:
        N_TRIALS = int(sys.argv[1])
    table3 = make_table3(testcases)
    with open("benchmarks_3.tex", 'w') as f:
        f.write(table3)

