# Coq Mechanization Artifact

[![DOI](https://zenodo.org/badge/771601216.svg)](https://zenodo.org/doi/10.5281/zenodo.11534019)


Code artifact for the paper *"Modular Verification of Intrusive List and Tree Data Structures in Separation Logic"*.

## Compilation

- Install [Coq](https://coq.inria.fr/download), [Iris](https://gitlab.mpi-sws.org/iris/iris/) and [Diaframe](https://gitlab.mpi-sws.org/iris/diaframe).
- Compile the project files by running `make` in the folder containing the make-file.

The files were originally complied with
- `coq` version `8.17.1`
- `iris` version `dev.2024-01-11.0.838322ad`
- `coq-diaframe` version `dev.2024-02-01.0.71a9cd50`
- `coq-diaframe-heap-lang` version `dev.2024-02-01.0.71a9cd50`


##  Instructions (using opam)

Recommended: Create a new `opam` switch 
```
opam switch create modular-intrusive 4.14.0
```
Use `opam switch` to check if you are on the newly created switch.
Make sure opam can find the Coq and Iris packages:
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin add coq 8.17.1
```
Install Diaframe and the required dependencies with:
```
opam install coq-diaframe
opam install coq-diaframe-heap-lang
```
