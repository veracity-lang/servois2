import sys
from os.path import join
import subprocess

exe = sys.argv[1]
timeout = 30
yml_dir = '../yamls/'

def test(yml, m1, m2, expected, additional_params=[]):
    cmd = (exe, 'synth', '-q', '--timeout', str(timeout), join(yml_dir, yml + '.yml'), m1, m2) + additional_params

    popen = subprocess.Popen(
        cmd, universal_newlines=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )
    out, err = popen.communicate()
    out = out.strip()
    
    # TODO: We can make this more sophisticated (e.g. SMT solve for logical equivalence), but this should work for sanity checking for now.
    # At least can report where to check further manually.
    if out == expected: return True, out
    else: return False, out


test_cases = [
    ('counter', 'increment', 'decrement', '(not (= contents 0))'),
    ('string', 'hasChar', 'concat', '(or (not (str.contains m2_concat_other m1_hasChar_chara)) (and (str.contains data m1_hasChar_chara) (str.contains m2_concat_other m1_hasChar_chara)))'),
    ('hashtable', 'put', 'get', '(or (and (member m2_get_k0 keys) (not (member m1_put_k0 keys))) (and (not (= m2_get_k0 m1_put_k0)) (not (= m1_put_v0 (select H m1_put_k0))) (member m1_put_k0 keys)) (and (= m1_put_v0 (select H m1_put_k0)) (member m1_put_k0 keys)))', '--prover=cvc4')
    ]

def main():
    results = []
    outputs = []
    for test_case in test_cases:
        res, out = test(*(test_case[:4]), test_case[4:])
        results.append(res)
        outputs.append(out)
    n_correct = sum(map(int, results))
    print(f"Test results: {n_correct}/{len(results)}")
    if not (n_correct is len(results)):
        print("Failed tests:")
        failed_tests = [y + (z,) for (x, y, z) in zip(results, test_cases, outputs) if not x]
        for failed_test in failed_tests:
            print(f"\tyaml: {failed_test[0]}, m1: {failed_test[1]}, m2: {failed_test[2]}; expected: {failed_test[3]}, got {failed_test[4]}.")


main()
