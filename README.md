# rustSAT
A DPLL SAT solver implemented in Rust for the COMP21111 SAT Solver Competition. 
Came 2nd place in competition amongst participants.
## Author
Pieter Ayal

## Compilation
To compile the solver on CS Linux machines, run:
```bash
rustc -O main.rs -o sat_solver
```

## Usage
```bash
./sat_solver < test.cnf
or 
cat test.cnf | ./sat_solver
```

## Implementation Details

### Language
Implemented in **Rust** for memory safety and performance as well as in effort to learn the language.

### Core Algorithm
DPLL Algorithm

### Optimizations Implemented

1. **Two-Watched Literals**
   - Each clause maintains two watched literals
   - Only checks clauses when a watched literal becomes false
   - Reduces unit propagation from O(clauses) to O(clauses_watching_literal)
   - Most impactful optimization for large instances

2. **Pure Literal Elimination**
   - Detects variables appearing in only one polarity
   - Assigns them immediately without branching
   - Applied once during preprocessing

3. **Unit Propagation (BCP)**
   - Boolean Constraint Propagation loop
   - Iteratively propagates unit clauses until fixpoint
   - Early termination when conflict detected

4. **Smart Variable Selection Heuristic**
   - Picks variables appearing most frequently in unsatisfied clauses
   - Prioritizes variables that are more constrained
   - Better than naive "first unassigned" approach

5. **Polarity Selection**
   - Chooses initial assignment based on occurrence frequency
   - Tries positive polarity first if variable appears more often positive

6. **Preprocessing Optimizations**
   - Tautology removal (clauses with both x and ¬x)
   - Clause sorting by length (smaller clauses checked first)
   - Precomputed literal occurrence counts

7. **Early Termination**
   - Stops checking literals in clause once satisfied
   - Breaks early in unit propagation when unit found

### Performance Notes
The two-watched literals scheme was the most significant optimization, providing substantial speedup on medium and hard instances. The combination of smart heuristics, small optimizations such as tautology elimination, pure literal and sorting and efficient data structures allows the solver to handle instances with thousands of variables and clauses efficiently.


## Permission
Yes, I agree for my solver and name to be included in the evaluation table on Canvas. 


```
