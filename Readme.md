The Monotone construction
---------------------------

This project formalizes the monotone construction for reasoning about monotonicity with respect to arbitrary preorder relations in separation logic.
There are three folders in this project: `iris-src`, `categorical`, and `monotone_counter`.


## `iris-src`

This folder includes the formalization of the monotone construction as an Iris resource algebra.
This resource algebra is defined in the file `iris-src/monotone.v`
The sub-folder `iris-src/examples` includes three examples of using the monotone resource algebra:

- `iris-src/examples/mon_ref.v` constructs monotone references that are associated with a preorder relation.
   A monotone reference can only be updated if they respect the associated preorder relation.
   Any Iris points-to proposition can be turned into a monotone reference and back into a an ordinary points-to proposition (possibly multiple times).

- `iris-src/examples/exclude_path.v` shows how the monotone resource algebra instantiated with a very simple preorder can be used to prove that certain paths in the program execution are unreachable.

- `iris-src/examples/causal-closure.v` is an example inspired by verification of causally consistent databases.
   It shows how the monotone resource algebra can be used to enforce a relation between ghost resources that allows us to prove that if an event is observed then any other event that it depends on is also observed.

### compile instructions

Use `make` in `iris-src` to compile the development. This development has the following dependencies:
1. Coq 8.12
2. The std++ project (Iris depends on this): commit hash: 63d07bb8e388bff552dc4985c4f363ccd5242269
3. The Iris program logic: commit hash: b2b558ac9e8b7d43e9e6e21a61dda3a19c1b62b2


## `categorical`

This folder formalizes the theory behind the monotone construction and establishes the canonicity of this construction.
In particular, it establishes that the monotone construction arises as a free functor.
The files in this development are as follows:

- `categorical/PreOrder.v` formalizes the category of preorder relations and monotone functions.
- `categorical/PartialOrder.v` formalizes the category of partial order relations and monotone functions. It also establishes that this category is a reflective subcategory of the category of preorders.
- `categorical/PCM.v` formalizes the category of partial commutative monoids. This file also formalizes the extension functor that maps a PCM to its extension order in the category of preorders.
- `categorical/lattice.v` formalizes the category of join-semilattices with a bottom element and shows that this category is a full subcategory of the category of partial commutative monoids.
- `categorical/monotone.v` formalizes the monotone construction as a construction that given a partial order relation constructs a join-semilattice with a bottom element.
- `categorical/adjunction.v` establishes that the monotone functor from the category of partial orders to the category of join-semilattices with a bottom element is the left adjoint to the forgetful functor.

### compile instructions

Use `make` in `categorical` to compile the development. This development has the following dependencies:
1. Coq 8.12
2. The category theory library: https://github.com/amintimany/Categories commit hash: 96ce5ad61a1078d8c8ac73befa33c147650caf4d

## `monotone-counter`

This folder verifies correctness of a monotone counter with basic iris resource algebras, i.e., without the monotone resource algebra.
This formalization serves as a simple example of how one reasons about monotonicity in separation logic.

### compile instructions

Use `make` in `iris-src` to compile the development. Dependencies for this development are exactly the same as the ones for the `iris-src` folder.