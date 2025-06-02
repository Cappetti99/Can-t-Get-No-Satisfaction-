import random
import numpy as np
import matplotlib
matplotlib.use('Agg')  # Usa backend non-interattivo per evitare errori Qt/Wayland
import matplotlib.pyplot as plt
from timeit import default_timer as timer
import os
import subprocess
import tempfile

os.makedirs('output', exist_ok=True)


def genera_formula_3sat(num_variabili, num_clausole):
    """Genera una formula 3-SAT casuale con il numero specificato di variabili e clausole."""
    formula = []
    
    for _ in range(num_clausole):
        dimensione_clausola = 3  # 3-SAT come specificato nel paper
        clausola = set()
        letterali_usati = []
        
        while len(clausola) < dimensione_clausola:
            # Seleziona una variabile casuale non ancora utilizzata in questa clausola
            while True:
                var_selezionata = random.randint(1, num_variabili)
                if var_selezionata not in letterali_usati:
                    letterali_usati.append(var_selezionata)
                    break
            
            # Decide casualmente se negare la variabile
            if random.choice([True, False]):
                var_selezionata = -var_selezionata
            
            clausola.add(var_selezionata)
        
        formula.append(list(clausola))
    
    return formula


def formula_to_dimacs(formula, num_variabili):
    """Converte una formula CNF nel formato DIMACS per MiniSAT."""
    num_clausole = len(formula)
    dimacs_lines = [f"p cnf {num_variabili} {num_clausole}"]
    
    for clausola in formula:
        clausola_str = " ".join(map(str, clausola)) + " 0"
        dimacs_lines.append(clausola_str)
    
    return "\n".join(dimacs_lines)


def risolvi_con_minisat(formula, num_variabili, modalita_debug=False):
    """Risolve una formula SAT usando MiniSAT esterno."""
    try:
        # Crea file temporanei per input e output
        with tempfile.NamedTemporaryFile(mode='w', suffix='.cnf', delete=False) as input_file:
            input_filename = input_file.name
            dimacs_content = formula_to_dimacs(formula, num_variabili)
            input_file.write(dimacs_content)
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.out', delete=False) as output_file:
            output_filename = output_file.name
        
        if modalita_debug:
            print(f"DIMACS content:\n{dimacs_content}")
            print(f"Input file: {input_filename}")
            print(f"Output file: {output_filename}")
        
        # Esegui MiniSAT
        try:
            result = subprocess.run([
                'minisat', input_filename, output_filename
            ], capture_output=True, text=True, timeout=30)
            
            if modalita_debug:
                print(f"MiniSAT return code: {result.returncode}")
                print(f"MiniSAT stdout: {result.stdout}")
                print(f"MiniSAT stderr: {result.stderr}")
            
            # Leggi il risultato
            try:
                with open(output_filename, 'r') as f:
                    output_content = f.read().strip()
                
                if modalita_debug:
                    print(f"MiniSAT output: {output_content}")
                
                lines = output_content.split('\n')
                if not lines:
                    return None
                
                # La prima riga contiene SAT o UNSAT
                status_line = lines[0].strip()
                
                if status_line == "SAT":
                    # Se c'è una seconda riga, contiene l'assegnamento
                    if len(lines) > 1:
                        assignment_line = lines[1].strip()
                        literals = assignment_line.split()
                        
                        assignment = {}
                        for lit in literals:
                            if lit != '0':  # '0' è il terminatore
                                var_num = abs(int(lit))
                                assignment[var_num] = int(lit) > 0
                        
                        return assignment
                    else:
                        # SAT ma nessun assegnamento specifico fornito
                        return {}
                elif status_line == "UNSAT":
                    return None
                else:
                    if modalita_debug:
                        print(f"Unexpected MiniSAT status: {status_line}")
                    return None
                    
            except FileNotFoundError:
                if modalita_debug:
                    print(f"Output file not found: {output_filename}")
                return None
                
        except subprocess.TimeoutExpired:
            if modalita_debug:
                print("MiniSAT timeout")
            return None
        except FileNotFoundError:
            print("ERRORE: MiniSAT non trovato. Assicurati che sia installato e nel PATH.")
            print("Su Ubuntu/Debian: sudo apt-get install minisat")
            print("Su macOS: brew install minisat")
            return None
        
    except Exception as e:
        if modalita_debug:
            print(f"Errore durante l'esecuzione di MiniSAT: {e}")
        return None
    finally:
        # Pulizia file temporanei
        try:
            os.unlink(input_filename)
            os.unlink(output_filename)
        except:
            pass


def semplifica_formula_booleana(formula_cnf, variabile_assegnata, valore_verita):
    """Semplifica la formula CNF dato un assegnamento di una variabile."""
    formula_risultante = []
    
    for clausola_corrente in formula_cnf:
        if valore_verita:  # variabile_assegnata = True
            if variabile_assegnata in clausola_corrente:
                continue  # Clausola soddisfatta, rimuovila
            nuova_clausola = [lit for lit in clausola_corrente if lit != -variabile_assegnata]
        else:  # variabile_assegnata = False
            if -variabile_assegnata in clausola_corrente:
                continue  # Clausola soddisfatta, rimuovila
            nuova_clausola = [lit for lit in clausola_corrente if lit != variabile_assegnata]
        
        if not nuova_clausola and nuova_clausola != clausola_corrente:
            return None  # Clausola vuota dopo semplificazione -> insoddisfacibile
        
        formula_risultante.append(nuova_clausola)
    
    return formula_risultante


def risolvi_con_backtracking(formula_cnf, lista_variabili, assegnamento_corrente, usa_euristiche, modalita_debug):
    """Risolve usando l'algoritmo di backtracking con opzionale propagazione unitaria."""
    if modalita_debug:
        print(f"Backtracking: formula={formula_cnf}, variabili={lista_variabili}, assegnamento={assegnamento_corrente}")
    
    # Caso base: formula vuota -> soddisfacibile
    if not formula_cnf:
        return assegnamento_corrente
    
    # Caso base: clausola vuota presente -> insoddisfacibile
    if any(not clausola for clausola in formula_cnf):
        return None
    
    # APPLICAZIONE EURISTICHE
    if usa_euristiche:
        # Propagazione Unitaria: trova clausole con un solo letterale
        clausole_unitarie = [clausola[0] for clausola in formula_cnf if len(clausola) == 1]
        
        for letterale_unitario in clausole_unitarie:
            if modalita_debug:
                print(f"Propagazione unitaria con clausola: {letterale_unitario}")
            
            if letterale_unitario > 0:
                formula_cnf = semplifica_formula_booleana(formula_cnf, letterale_unitario, True)
                assegnamento_corrente[letterale_unitario] = True
            else:
                formula_cnf = semplifica_formula_booleana(formula_cnf, -letterale_unitario, False)
                assegnamento_corrente[-letterale_unitario] = False
            
            if formula_cnf is None:
                return None  # Conflitto durante propagazione unitaria
            
            if abs(letterale_unitario) in lista_variabili:
                lista_variabili.remove(abs(letterale_unitario))
        
        if not lista_variabili:
            return assegnamento_corrente
    
    # ALGORITMO SAT CLASSICO
    variabile_da_provare = lista_variabili[0]
    variabili_rimanenti = lista_variabili[1:]
    
    # Prova ad assegnare True alla variabile
    nuovo_assegnamento = assegnamento_corrente.copy()
    nuovo_assegnamento[variabile_da_provare] = True
    formula_semplificata = semplifica_formula_booleana(formula_cnf, variabile_da_provare, True)
    
    if modalita_debug:
        print(f"Provo variabile {variabile_da_provare} = True, formula semplificata: {formula_semplificata}")
    
    if formula_semplificata is not None:
        risultato = risolvi_con_backtracking(formula_semplificata, variabili_rimanenti, nuovo_assegnamento, 
                                           usa_euristiche, modalita_debug)
        if risultato is not None:
            return risultato
    
    # Prova ad assegnare False alla variabile
    nuovo_assegnamento[variabile_da_provare] = False
    formula_semplificata = semplifica_formula_booleana(formula_cnf, variabile_da_provare, False)
    
    if modalita_debug:
        print(f"Provo variabile {variabile_da_provare} = False, formula semplificata: {formula_semplificata}")
    
    if formula_semplificata is not None:
        risultato = risolvi_con_backtracking(formula_semplificata, variabili_rimanenti, nuovo_assegnamento, 
                                           usa_euristiche, modalita_debug)
        if risultato is not None:
            return risultato
    
    return None  # Insoddisfacibile


def verifica_soddisfacibilita(clausole_formula, numero_variabili, applica_euristiche, debug_attivo, usa_minisat=False):
    """Verifica se una formula 3-SAT è soddisfacibile."""
    if usa_minisat:
        return risolvi_con_minisat(clausole_formula, numero_variabili, debug_attivo)
    else:
        variabili_disponibili = list(range(1, numero_variabili + 1))
        assegnamento_iniziale = {}
        return risolvi_con_backtracking(clausole_formula, variabili_disponibili, assegnamento_iniziale, 
                                      applica_euristiche, debug_attivo)


def test_probabilita_soddisfacibilita(num_var, lista_num_clausole, num_esperimenti, euristiche_attive, usa_minisat=False):
    """Testa la probabilità di soddisfacibilità per diversi rapporti clausole/variabili."""
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
        print(f"[{solver_name}] N: {num_var}, Rapporto: {rapporto_corrente:.2f}, Tempo medio: {tempo_medio:.6f}s")
        
        tempi_esecuzione.append(tempo_medio)
        percentuali_soddisfatte.append(percentuale_soddisfatta)
    
    return rapporti_m_n, percentuali_soddisfatte, tempi_esecuzione


def analisi_distribuzione_soddisfacibilita(num_var, lista_num_clausole, punti_per_rapporto, euristiche_attive, usa_minisat=False):
    """Analizza la distribuzione dei tempi di esecuzione per ogni singolo test."""
    rapporti_tutti = []
    tempi_tutti = []
    risultati_sat = []
    
    for m_clausole in lista_num_clausole:
        rapporto_corrente = m_clausole / num_var
        solver_name = "MiniSAT" if usa_minisat else ("SAT+Euristiche" if euristiche_attive else "SAT")
        print(f"[{solver_name}] Rapporto corrente: {rapporto_corrente:.2f}")
        
        for _ in range(punti_per_rapporto):
            formula_test = genera_formula_3sat(num_var, m_clausole)
            
            inizio_tempo = timer()
            risultato_sat = verifica_soddisfacibilita(formula_test, num_var, euristiche_attive, False, usa_minisat)
            fine_tempo = timer()
            
            rapporti_tutti.append(rapporto_corrente)
            tempi_tutti.append(fine_tempo - inizio_tempo)
            
            if risultato_sat is not None:
                risultati_sat.append(1)
            else:
                risultati_sat.append(0)
    
    return rapporti_tutti, tempi_tutti, risultati_sat


if __name__ == "__main__":
    
    debug_attivo = False
    euristiche_abilitate = True
    use_minisat = True  # NUOVA VARIABILE PER ATTIVARE MINISAT
    
    if use_minisat:
        # Parametri ottimizzati per MiniSAT (più veloce)
        valori_n_variabili = [10, 20, 30, 40]
        numero_test = 100
        variabili_per_test_dettagliato = 40
    elif euristiche_abilitate:
        valori_n_variabili = [10, 20, 30, 40]
        numero_test = 100
        variabili_per_test_dettagliato = 40
    else:
        valori_n_variabili = [10, 20, 30, 40]
        numero_test = 100
        variabili_per_test_dettagliato = 40
    
    palette_colori = ["#e41a1c", "#377eb8", "#4daf4a", "#984ea3", "#ff7f00", "#ffff33"]
    
    punti_per_rapporto = 50
    
    genera_grafico_probabilita = True
    genera_grafico_distribuzione = True
    
    if genera_grafico_probabilita:
        indice_colore = 0
        rapporti_salvati = []
        tempi_salvati = []
        
        for variabili in valori_n_variabili:
            clausole_da_testare = np.arange(variabili, (variabili * 9) + 1, int(variabili / 10))
            rapporti, percentuali, tempi = test_probabilita_soddisfacibilita(variabili, clausole_da_testare, 
                                                                           numero_test, euristiche_abilitate, use_minisat)
            
            tempi_salvati.append(tempi)
            rapporti_salvati.append(rapporti)
            
            plt.scatter(rapporti, percentuali, color=palette_colori[indice_colore], s=25, alpha=0.5, 
                       label=f"N = {variabili}")
            indice_colore += 1
        
        # Titolo e nome file basati sul solver utilizzato
        if use_minisat:
            titolo_prob = 'Percentuale soddisfacibili con MiniSAT'
            nome_file_prob = 'output/plt_prob_MiniSAT.png'
            nome_file_prob_pdf = 'output/plt_prob_MiniSAT.pdf'
        elif euristiche_abilitate:
            titolo_prob = 'Percentuale soddisfacibili con Euristiche'
            nome_file_prob = 'output/plt_prob_H.png'
            nome_file_prob_pdf = 'output/plt_prob_H.pdf'
        else:
            titolo_prob = 'Percentuale soddisfacibili senza Euristiche'
            nome_file_prob = 'output/plt_prob.png'
            nome_file_prob_pdf = 'output/plt_prob.pdf'
        
        plt.title(titolo_prob)
        plt.xlabel('Rapporto Test M/N')
        plt.ylabel('Percentuale soddisfacibili')
        plt.grid(True)
        plt.legend()
        plt.ylim(0, 100)
        plt.xlim(1, 9)
        plt.xticks(range(1, 10, 1))
        
        plt.savefig(nome_file_prob)
        plt.savefig(nome_file_prob_pdf)
        plt.close()
        
        # Grafico tempi di esecuzione
        indice_colore = 0
        for idx in range(len(tempi_salvati)):
            plt.scatter(rapporti_salvati[idx], tempi_salvati[idx], color=palette_colori[indice_colore], 
                       s=25, alpha=0.5, label=f"N = {valori_n_variabili[idx]}")
            indice_colore += 1
        
        if use_minisat:
            titolo_tempi = 'Tempi di esecuzione medi con MiniSAT'
            nome_file_tempi = 'output/plt_times_MiniSAT.png'
            nome_file_tempi_pdf = 'output/plt_times_MiniSAT.pdf'
        elif euristiche_abilitate:
            titolo_tempi = 'Tempi di esecuzione medi con Euristiche'
            nome_file_tempi = 'output/plt_times_H.png'
            nome_file_tempi_pdf = 'output/plt_times_H.pdf'
        else:
            titolo_tempi = 'Tempi di esecuzione medi senza Euristiche'
            nome_file_tempi = 'output/plt_times.png'
            nome_file_tempi_pdf = 'output/plt_times.pdf'
        
        plt.title(titolo_tempi)
        plt.xlabel('Rapporto Test M/N')
        plt.ylabel('Tempi di esecuzione medi')
        plt.grid(True)
        plt.legend()
        plt.xlim(1, 9)
        plt.xticks(range(1, 10, 1))
        
        plt.savefig(nome_file_tempi)
        plt.savefig(nome_file_tempi_pdf)
        plt.close()
    
    if genera_grafico_distribuzione:
        clausole_dettagliate = np.arange(variabili_per_test_dettagliato, 
                                       (variabili_per_test_dettagliato * 9) + 1, 
                                       int(variabili_per_test_dettagliato / 10))
        
        rapporti_dist, tempi_dist, risultati_dist = analisi_distribuzione_soddisfacibilita(
            variabili_per_test_dettagliato, clausole_dettagliate, punti_per_rapporto, euristiche_abilitate, use_minisat)
        
        for i in range(len(rapporti_dist)):
            colore_punto = "royalblue" if risultati_dist[i] == 1 else "orangered"
            plt.scatter(rapporti_dist[i], tempi_dist[i], color=colore_punto, s=18, alpha=0.60)
        
        if use_minisat:
            titolo_dist = f'Tempo di esecuzione N = {variabili_per_test_dettagliato} con MiniSAT'
            nome_file_sat = 'output/plt_sat_MiniSAT.png'
            nome_file_sat_pdf = 'output/plt_sat_MiniSAT.pdf'
        elif euristiche_abilitate:
            titolo_dist = f'Tempo di esecuzione N = {variabili_per_test_dettagliato} con Euristiche'
            nome_file_sat = 'output/plt_sat_H.png'
            nome_file_sat_pdf = 'output/plt_sat_H.pdf'
        else:
            titolo_dist = f'Tempo di esecuzione N = {variabili_per_test_dettagliato} senza Euristiche'
            nome_file_sat = 'output/plt_sat.png'
            nome_file_sat_pdf = 'output/plt_sat.pdf'
        
        plt.title(titolo_dist)
        plt.xlabel('Rapporto Test M/N')
        plt.ylabel('Tempo di esecuzione')
        plt.grid(True)
        plt.xlim(1, 9)
        plt.xticks(range(1, 10, 1))
        
        plt.savefig(nome_file_sat)
        plt.savefig(nome_file_sat_pdf)
        plt.close()

    print("Analisi completata!")
    if use_minisat:
        print("Risultati MiniSAT salvati con suffisso '_MiniSAT'")
    elif euristiche_abilitate:
        print("Risultati con euristiche salvati con suffisso '_H'")
    else:
        print("Risultati senza euristiche salvati senza suffisso")
