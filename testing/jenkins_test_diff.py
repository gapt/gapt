#!/usr/bin/env python3
import sys
from bs4 import BeautifulSoup
from collections import defaultdict
import urllib.request, urllib.parse

_, build_number_old, build_number_new = sys.argv

print('Comparing jenkins build {0} and {1}'.format(build_number_old, build_number_new))

state_renaming = {
        'Passed': 'Pass',
        'Regression': 'Fail',
        'Failed': 'Fail',
        'Fixed': 'Pass',
        'Skipped': 'Skip',
        }

tests = [ 'Prover9TestCase/'+s for s in ('<all>', 'import', 'minisat validity', 'solvePropositional', 'expansionProofToLKProof', 'verit validity') ] \
        + [ 'VeriTTestCase/'+s for s in ('<all>', 'import', 'minisat validity') ] \
        + [ 'LeanCoPTestCase/'+s for s in ('<all>', 'import', 'minisat validity') ]

def get_test_results(build_no, test_case_step):
    url = 'http://compile:8080/job/{0}/{1}/testReport/{2}/' \
            .format(*map(urllib.parse.quote, [ 'gapt extended testing', build_no, test_case_step ]))
    return urllib.request.urlopen(url).read()

def parse_jenkins(f, prefix=''):
    test_states = {}
    for test in BeautifulSoup(f).find(id='testresult').find_all('tr')[1:]:
        name, duration, state = test.find_all('td')
        test_states[prefix+name.text] = state_renaming[state.text]
    return test_states

old_test_states = {}
new_test_states = {}

for test in tests:
    print('Downloading results for {0}...'.format(test))

    prefix = test+'/'
    old_test_states.update(parse_jenkins(get_test_results(build_number_old, test), prefix))
    new_test_states.update(parse_jenkins(get_test_results(build_number_new, test), prefix))

transitions = defaultdict(list)
for test_name in old_test_states.keys() | new_test_states.keys():
    old_state = old_test_states.get(test_name, 'Missing')
    new_state = new_test_states.get(test_name, 'Missing')
    transitions[(old_state, new_state)].append(test_name)

print('Summary:')
for (old_state, new_state), test_names in sorted(transitions.items()):
    if old_state != new_state:
        print('  - {0} -> {1}: {2} tests'.format(old_state, new_state, len(test_names)))

for (old_state, new_state), test_names in sorted(transitions.items()):
    if old_state != new_state:
        print('\n{0} -> {1}:'.format(old_state, new_state))
        for n in test_names:
            print('  - {0}'.format(n))
