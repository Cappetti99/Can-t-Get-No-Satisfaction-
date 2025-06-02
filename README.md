# Can't Get No Satisfaction - 3-SAT Experimental Analysis

This project explores the **satisfiability of 3-SAT formulas** through experimental simulations using different solving strategies. Inspired by computational complexity theory and the analogy with **phase transitions in physics**, we compare the behavior of:

- **Naive Backtracking**
- **Backtracking with Unit Propagation Heuristic**
- **MiniSAT**, a state-of-the-art industrial SAT solver

## 📌 Key Concepts

- **3-SAT Problem**: A Boolean satisfiability problem where each clause has exactly 3 literals. It was the first known **NP-complete** problem.
- **Clause-to-variable ratio (M/N)**: Crucial for identifying the **phase transition** from satisfiable to unsatisfiable instances.
- **Unit Propagation**: A heuristic that simplifies the formula when a clause has only one literal, reducing the search space.
- **Phase Transition**: Analogous to physical systems (e.g. the Ising model), where the transition occurs sharply around a critical M/N ≈ 4.2.

## 🧪 Experimental Setup

For each combination of parameters:

- Generate random 3-SAT formulas.
- Test satisfiability using one of the three methods.
- Collect statistics on:
  - **Execution time**
  - **Satisfiability probability**
  - **Computational effort**

### Parameters

- Number of variables `N`: 10 to 160
- Clause-to-variable ratio `M/N`: from 1 to 9
- Number of experiments per setting: customizable (e.g., 100)

## 🛠️ Code Structure

### Formula Generation
- `genera_formula_3sat(n, m)`: Generates random 3-SAT formulas.
- `formula_to_dimacs(...)`: Converts to DIMACS format (for MiniSAT).

### Solvers
- `risolvi_con_backtracking(...)`: Recursive backtracking solver with optional heuristics.
- `risolvi_con_minisat(...)`: Invokes MiniSAT via subprocess.

### Evaluation
- `test_probabilita_soddisfacibilita(...)`: Estimates probability of satisfiability as M/N increases.
- `analisi_distribuzione_soddisfacibilita(...)`: Collects execution time distributions.

### Utilities
- `semplifica_formula_booleana(...)`: Simplifies CNF formulas after a variable assignment.

## 📈 Results

### 📌 Phase Transition Behavior
All methods confirm the phase transition near **M/N ≈ 4.2**:
- For **low M/N**, most formulas are satisfiable.
- For **high M/N**, most formulas become unsatisfiable.
- The transition is **sharper** for higher `N`.

### 🧠 Heuristics Help
- **Unit Propagation** drastically reduces runtime near the critical region.
- It also reduces the number of recursive calls.

### 🚀 MiniSAT Advantage
- By far the **fastest** and most **robust**.
- Scales efficiently to formulas with hundreds of variables.
- Suitable for benchmarking or validating other solvers.

## 📊 Output

The project generates plots saved in the `output/` folder:

- **Probability of satisfiability** vs M/N ratio
- **Average execution time** vs M/N
- **Execution time distribution** (colored by SAT/UNSAT outcome)

## 📦 Requirements

- Python 3.8+
- `numpy`
- `matplotlib`
- **MiniSAT** installed and accessible in PATH:
  - Ubuntu/Debian: `sudo apt install minisat`
  - macOS (Homebrew): `brew install minisat`

## ▶️ Running the Project

```bash
python3 main.py
