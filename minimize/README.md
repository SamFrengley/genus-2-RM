This directory contains the files in which we implement the algorithms from Section 5. Below we list the key intrinsics in each file.

## `minimization.m`
This is the central file in this directory, and it provides the main intrinsics.

### `MinimizationSearch`
Our main intrinsic, which takes as input a homogeneous quadratic form `L` in 3 variables and applies Algorithm 5.5 (known in the text also as `MinimizationSearch`) to attempt to find a minimal model for the conic defined by `L`. Optional arguments:
- `maxsteps:=100` an integer which bounds the maximum number of steps the algorithm will take before returning a failure.
- `method:="slope"` a string which determines the scoring method as:
  - `"slope"`: Average slope score.
  - `"deg1"`: Degree score with linear penalty for number of times this score appeared along this path.
  - `"deg2"`: Degree score with square penalty for number of times this score appeared along this path.
  - `"alt"`: Alternate between slope and deg2.
  - `"fwd"`: Forward-looking score (slow).
- `randomization=false` a boolean which, if set to `true`, indicates that random jumps will be taken as described in Remark 5.9(3).
- Verbose output is controlled by `ConicMinimize` which takes values 0, 1, and 2. If `MinimizationSearch` is run after `SetVerbose("ConicMinimize", 2);` then information will be given at every minimization step.
  
## Other files

- `mestre-conic-cubic.m`: This file contains intrinsics to compute the (IC or RM simplified) Mestre conic and cubic as defined in Section 4. The intrinsics of note are:
  - `MestreConic`, `MestreCubic`, and `MestreConicCubic` which output Mestre's original $L$ and $M$ on input Igusa--Clebsch invariants.
  - `ICConic`, `ICCubic`, and `ICConicCubic` which output IC simplified $L$ and $M$ on input Igusa--Clebsch invariants.
  - `RMConic`, `RMCubic`, and `RMConicCubic` which output RM simplified $L$ and $M$ on input Elkies--Kumar's `A,A1,B,B1,B2`.

- `good-coords.m`: This file contains some hacky functions which attempt to find $\mathrm{PGL}_2$ changes of coordinates to the base copy of $\mathbb{A}^2$ which make the problem "nicer" in some way.
  - Some functionality which would be good to add is to use $\mathrm{Bir}_{\mathbb{Q}} \mathbb{A}^2$ to make "nice" coordiante choices (maybe start with Cremona transformations centred at singular points of interesting curves).