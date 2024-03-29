# Reflective Generators

Code Artifact for "Reflecting on Random Generation" ICFP23 paper.

## Reuse

This repository will need to be reorganized slightly before submission to Hackage, but the core
reusable components are easy to get started with. Simply importing `Reflectives` along with
`Interps` (for the appropriate interpretation) gives you all the tools you need to write and use
your own reflective generators.

## Replication

This section describes how to replicate the results in the paper.

### Requirements

Library dependencies are managed by `stack`, which you can install via
[ghcup](https://www.haskell.org/ghcup/) (recommended) or from
[the stack website](https://docs.haskellstack.org/en/stable/) (simpler).

To run the python analysis code, ensure you have a version of Python 3 on your system (modern
versions of Linux ship with `python3` by default). Then install `pip`; on Ubuntu:
```
sudo apt install python3-pip
```
Finally, install a few packages:
```
python3 -m pip install numpy seaborn
```

These dependencies are already installed in the replication VM.

### Code Tour

This will take you through what code we have, in reference to what appears in the paper.

> - `analysis/`
>   * `json/` _contains 10 JSONs for IFH experiment (Figure 7)_
>   * `shrinks/` _used to collect Hypothesis experiment results for Table 1_
>   * `json_analysis.py` _generates plots for IFH experiment_
>   * `json_analysis.ipynb` _generates plots for IFH experiment, workbook version_
> - `app/` _contains main file for Hypothesis experiment (Table 1)_
> - `json-app/` _contains main file for IFH experiment (Figure 7)_
> - `package-json-app/` _contains main file for realistic shrinking example (Section 6.2)_
> - `examples/`
>   * `demo.json` _json file used in package.json example_
>   * `demo-min.json` _minified version of demo_
> - `src/`
>   * `Reflectives.hs` - the main definitions inc:
>     - Fig 1. `bst` example
>     - Fig 2. definitions
>     - `comap`
>     - `R` / `Reflective`
>     - DSL for creating Reflective Generators
>   * `Interps.hs` - the interpretations of Reflective Generators inc:
>     - `generate` (Fig 4)
>     - `reflect` (Fig 5)
>     - `choices`
>     - `genWithWeights` (renamed to `weighted`)
>     - completers / producers
>   * `Choices.hs` - code specific to the shrinking and choices interps
>   * `FanOut.hs` - examples of the fan out property
>   * `Nats.hs` - examples of generator overlap (Fig 6)
>   * `PolymorphicInterp.hs` - Interpretation of a Reflective Generator as a generic PMP
>   * `Examples/`
>     - `Hypothesis/` _contains the Reflective Generators for the Hypothesis experiment (Table 1)_
>     - `Hypothesis.hs` - Hypothesis experiment code
>     - `DivZero.hs` - Example Reflective Generator for terms where division by zero is avoided (Section 4.3).
>     - `JSON.hs` - defines a Reflective Generator for JSOn files inc `withHashCode`, renamed to `withChecksum`
>     - `PackageJSON.hs` - defines a Reflective Generator 'package' for package.json files
>     - `STLC.hs` - defines a Reflective Generator for the STLC
>     - `SystemF.hs` - defines a Reflective Generator for the SystemF
>     - `SystemFImplementation.hs` - contains an implementation of SystemF
> - `test/` _contains testing file to demonstrate testing correctness of Reflective Generators inc:_
>   * Def 2: soundness
>   * Def 5: pure proj
>   * Def 6: externally sound
>   * Def 7: externally complete
> - then at the tip level we also have Haskell project stuff:
>   * `package.yaml`
>   * `reflective-minimal.cabal`
>   * `Setup.hs`
>   * `stack.yaml`
>   * `stack.yaml.lock`
> - and some generic project stuff:
>   * `README.md`
>   * `LICENSE`
>   * `.gitignore`

### Recreating Results

This will provide a step-by-step as to how to recreate the following results from our paper:
  1. Testing the correctness of Reflective Generators (Section 4.1 _Correctness of a Reflective Generator._)
  2. Analysis of IFH-style generator (Figure 7)
  3. Replicating the Hypothesis Experiment to analyze the Shrinking of Reflective Generators (Table 1)
  4. Using our of shrinking JSON files (Section 6.2 _A Realistic Example_)

#### 1. Testing the correctness of Reflective Generators

Run the following command from the root directory of this project:
```bash
stack test
```

#### 2. Analysis of IFH-style generator

To generate the data from our Inputs From Hell evaluation, first generate the data by running:
```
stack run json-exe
```
This reads from `analysis/json` and trains a generator to replicate the examples in that directory.

Then, you can either run
```
cd analysis; python3 json_analysis.py
```
To generate the plots as `pdf` files, or you can play around with `json_analysis.ipynb` as a
notebook.

Note: if you are generating the PDFs in the VM, you can copy them to your computer by running the
following command **outside the VM**:
```
scp -P 5555 artifact@localhost:reflective-minimal/analysis/<desired_chart>.pdf .
```

### 3. Replicating the Hypothesis Experiment to analyze the Shrinking of Reflective Generators (Table 1)

Run the following command from the root directory of this project:
```bash
stack run reflective-minimal-exe
```
Note that this is slow (it takes around 15 minutes on our machines, since it runs a lot of trials),
and that the output is printed to the terminal in format:
```
experiment: unshrink mean (unshrink stddev range) & QC.genericShrink mean (QC.genericShrink stddev range) & reflective mean (reflective stddev range)
```
e.g.
```
heap: 15.06 (6.74--23.38) & 9.10 (8.23--9.97) & 9.18 (7.96--10.39)
```
where the first value is the unshrunk example, the second is the result of QuickCheck's generic
shrink, and the last is the result of the Reflective Generator's shrink.

(Note that the Hypothesis numbers in the paper are not re-run, but taken directly from their experiment.)

### 4. Replicating the package.json shrinking example.

Build the project and then `cat` `demo-min.json` into the `package-json-exe` shrinker program.

```
cat examples/demo-min.json | stack run -- package-json-exe
```

This prints the shrunken example, as shown in the paper.