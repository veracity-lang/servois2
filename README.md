# Servois2: Automatic Synthesis of Commutativity Conditions

## How to use from the command line

1. TL;DR: `cd src && make && make test`

1. Otherwise, to run a single example, create (or reuse an existing) input in the form of a YAML file (see yamls/hashtable.yml). Then execute:

``
./servois2 synth ../yamls/set.yml add contains
``

## How to use as a Library

1. Servois2 can be used as an OCaml library:

```
Servois2.Choose.choose := Servois2.Choose.poke2;
let phi, _ = Servois2.Synth.synth spec m1 m2 in
    Printf.eprintf "%f, %f, %f, %d, %b\n" 
	(!Servois2.Synth.last_benchmarks.time)
	(!Servois2.Synth.last_benchmarks.synth_time)
	(!Servois2.Synth.last_benchmarks.lattice_construct_time)
	(!Servois2.Synth.last_benchmarks.n_atoms)
	(!Servois2.Synth.last_benchmarks.answer_incomplete)
```

Or the `.verify` method can similarly be used.

## Previous versions

OCaml reworking of [Servois](https://github.com/kbansal/servois)
Some of the files in the yamls/ directory are taken from Servois.
For these files, the license in the yamls folder (BSD 3-Clause) applies.

## Model Counting
To use the model counting mode of Servois2, [ABC](https://github.com/vlab-cs-ucsb/ABC) must be installed.
