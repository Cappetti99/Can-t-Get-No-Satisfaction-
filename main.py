import random
import numpy as np
import matplotlib

# Use a non-interactive backend for matplotlib (to avoid display issues on some systems)
matplotlib.use('Agg')
import matplotlib.pyplot as plt

from timeit import default_timer as timer
import os
import subprocess
import tempfile

# Create the output directory if it doesn't already exist
os.makedirs('output', exist_ok=True)

# Generate a random 3-SAT formula with the given number of variables and clauses
def genera_formula_3sat(num_variabili, num_clausole):
    formula = []
    for _ in range(num_clausole):
        dimensione_clausola = 3  # Enforce 3-literal clauses (3-SAT)
        clausola = set()
        letterali_usati = []
        while len(clausola) < dimensione_clausola:
            # Pick a variable not used yet in the clause
            while True:
                var_selezionata = random.randint(1, num_variabili)
                if var_selezionata not in letterali_usati:
                    letterali_usati.append(var_selezionata)
                    break
            # Randomly negate the variable
            if random.choice([True, False]):
                var_selezionata = -var_selezionata
            clausola.add(var_selezionata)
        formula.append(list(clausola))
    return formula

# Convert a CNF formula to DIMACS format for use with MiniSAT
def formula_to_dimacs(formula, num_variabili):
    num_clausole = len(formula)
    dimacs_lines = [f"p cnf {num_variabili} {num_clausole}"]
    for clausola in formula:
        clausola_str = " ".join(map(str, clausola)) + " 0"
        dimacs_lines.append(clausola_str)
    return "\n".join(dimacs_lines)

# Solve a SAT formula using the external MiniSAT solver
def risolvi_con_minisat(formula, num_variabili, modalita_debug=False):
    try:
        # Create temp files for MiniSAT input and output
        with tempfile.NamedTemporaryFile(mode='w', suffix='.cnf', delete=False) as input_file:
            input_filename = input_file.name
            dimacs_content = formula_to_dimacs(formula, num_variabili)
            input_file.write(dimacs_content)
        with tempfile.NamedTemporaryFile(mode='w', suffix='.out', delete=False) as output_file:
            output_filename = output_file.name
        if modalita_debug:
            print(f"DIMACS content:\n{dimacs_content}")
        try:
            # Run MiniSAT on the CNF file
            result = subprocess.run(['minisat', input_filename, output_filename],
                                    capture_output=True, text=True, timeout=30)
            if modalita_debug:
                print(f"MiniSAT stdout: {result.stdout}")
            # Read MiniSAT output
            with open(output_filename, 'r') as f:
                output_content = f.read().strip()
            lines = output_content.split('\n')
            if not lines:
                return None
            status_line = lines[0].strip()
            if status_line == "SAT":
                if len(lines) > 1:
                    assignment_line = lines[1].strip()
                    literals = assignment_line.split()
                    assignment = {}
                    for lit in literals:
                        if lit != '0':
                            var_num = abs(int(lit))
                            assignment[var_num] = int(lit) > 0
                    return assignment
                else:
                    return {}
            elif status_line == "UNSAT":
                return None
            else:
                return None
        except subprocess.TimeoutExpired:
            return None
        except FileNotFoundError:
            print("ERROR: MiniSAT not found. Install it and ensure it's in your PATH.")
            return None
    except Exception as e:
        return None
    finally:
        # Clean up temporary files
        try:
            os.unlink(input_filename)
            os.unlink(output_filename)
        except:
            pass

# Simplify a CNF formula given a variable assignment
def semplifica_formula_booleana(formula_cnf, variabile_assegnata, valore_verita):
    formula_risultante = []
    for clausola_corrente in formula_cnf:
        if valore_verita:
            if variabile_assegnata in clausola_corrente:
                continue
            nuova_clausola = [lit for lit in clausola_corrente if lit != -variabile_assegnata]
        else:
            if -variabile_assegnata in clausola_corrente:
                continue
            nuova_clausola = [lit for lit in clausola_corrente if lit != variabile_assegnata]
        if not nuova_clausola and nuova_clausola != clausola_corrente:
            return None  # Clause is unsatisfiable
        formula_risultante.append(nuova_clausola)
    return formula_risultante

# Recursive backtracking SAT solver with optional unit propagation
def risolvi_con_backtracking(formula_cnf, lista_variabili, assegnamento_corrente, usa_euristiche, modalita_debug):
    if not formula_cnf:
        return assegnamento_corrente
    if any(not clausola for clausola in formula_cnf):
        return None
    if usa_euristiche:
        clausole_unitarie = [clausola[0] for clausola in formula_cnf if len(clausola) == 1]
        for letterale_unitario in clausole_unitarie:
            if letterale_unitario > 0:
                formula_cnf = semplifica_formula_booleana(formula_cnf, letterale_unitario, True)
                assegnamento_corrente[letterale_unitario] = True
            else:
                formula_cnf = semplifica_formula_booleana(formula_cnf, -letterale_unitario, False)
                assegnamento_corrente[-letterale_unitario] = False
            if formula_cnf is None:
                return None
            if abs(letterale_unitario) in lista_variabili:
                lista_variabili.remove(abs(letterale_unitario))
        if not lista_variabili:
            return assegnamento_corrente
    variabile_da_provare = lista_variabili[0]
    variabili_rimanenti = lista_variabili[1:]
    nuovo_assegnamento = assegnamento_corrente.copy()
    nuovo_assegnamento[variabile_da_provare] = True
    formula_semplificata = semplifica_formula_booleana(formula_cnf, variabile_da_provare, True)
    if formula_semplificata is not None:
        risultato = risolvi_con_backtracking(formula_semplificata, variabili_rimanenti, nuovo_assegnamento,
                                             usa_euristiche, modalita_debug)
        if risultato is not None:
            return risultato
    nuovo_assegnamento[variabile_da_provare] = False
    formula_semplificata = semplifica_formula_booleana(formula_cnf, variabile_da_provare, False)
    if formula_semplificata is not None:
        risultato = risolvi_con_backtracking(formula_semplificata, variabili_rimanenti, nuovo_assegnamento,
                                             usa_euristiche, modalita_debug)
        if risultato is not None:
            return risultato
    return None

# Entry point to verify satisfiability with optional heuristics or MiniSAT
def verifica_soddisfacibilita(clausole_formula, numero_variabili, applica_euristiche, debug_attivo, usa_minisat=False):
    if usa_minisat:
        return risolvi_con_minisat(clausole_formula, numero_variabili, debug_attivo)
    else:
        variabili_disponibili = list(range(1, numero_variabili + 1))
        assegnamento_iniziale = {}
        return risolvi_con_backtracking(clausole_formula, variabili_disponibili, assegnamento_iniziale,
                                        applica_euristiche, debug_attivo)

# Run experiments to estimate satisfiability probability vs clause-to-variable ratio
def test_probabilita_soddisfacibilita(num_var, lista_num_clausole, num_esperimenti, euristiche_attive, usa_minisat=False):
    rapporti_m_n = []
    percentuali_soddisfatte = []
    tempi_esecuzione = []
    for m_clausole in lista_num_clausole:
        rapporto_corrente = m_clausole / num_var
        rapporti_m_n.append(rapporto_corrente)
        contatore_soddisfatte = 0
        tempo_totale = 0
        for _ in range(num_esperimenti):
            formula_test = genera_formula_3sat(num_var, m_clausole)
            inizio_tempo = timer()
            risultato_sat = verifica_soddisfacibilita(formula_test, num_var, euristiche_attive, False, usa_minisat)
            fine_tempo = timer()
            tempo_totale += (fine_tempo - inizio_tempo)
            if risultato_sat is not None:
                contatore_soddisfatte += 1
        tempo_medio = tempo_totale / num_esperimenti
        percentuale_soddisfatta = (contatore_soddisfatte / num_esperimenti) * 100
        solver_name = "MiniSAT" if usa_minisat else ("SAT+Euristiche" if euristiche_attive else "SAT")
        print(f"[{solver_name}] N: {num_var}, Ratio: {rapporto_corrente:.2f}, Avg Time: {tempo_medio:.6f}s")
        tempi_esecuzione.append(tempo_medio)
        percentuali_soddisfatte.append(percentuale_soddisfatta)
    return rapporti_m_n, percentuali_soddisfatte, tempi_esecuzione

# Analyze execution time distribution over multiple formulas at each ratio
def analisi_distribuzione_soddisfacibilita(num_var, lista_num_clausole, punti_per_rapporto, euristiche_attive, usa_minisat=False):
    rapporti_tutti = []
    tempi_tutti = []
    risultati_sat = []
    for m_clausole in lista_num_clausole:
        rapporto_corrente = m_clausole / num_var
        solver_name = "MiniSAT" if usa_minisat else ("SAT+Euristiche" if euristiche_attive else "SAT")
        print(f"[{solver_name}] Current ratio: {rapporto_corrente:.2f}")
        for _ in range(punti_per_rapporto):
            formula_test = genera_formula_3sat(num_var, m_clausole)
            inizio_tempo = timer()
            risultato_sat = verifica_soddisfacibilita(formula_test, num_var, euristiche_attive, False, usa_minisat)
            fine_tempo = timer()
            rapporti_tutti.append(rapporto_corrente)
            tempi_tutti.append(fine_tempo - inizio_tempo)
            risultati_sat.append(1 if risultato_sat is not None else 0)
    return rapporti_tutti, tempi_tutti, risultati_sat
