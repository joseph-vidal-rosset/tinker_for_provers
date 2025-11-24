% =========================================================================
% OPERATEURS COMMUNS - Module centralise
% A inclure dans tous les modules du prouveur
% =========================================================================
:- use_module(library(lists)).
:- use_module(library(statistics)).
:- use_module(library(terms)).
% =========================================================================
% OPERATEURS TPTP (syntaxe d'entree)
% =========================================================================
:- op( 500, fy, ~).             % negation
:- op(1000, xfy, &).            % conjunction
:- op(1100, xfy, '|').          % disjunction
:- op(1110, xfy, =>).           % conditional
:- op(1120, xfy, <=>).          % biconditional
:- op( 500, fy, !).             % universal quanti
:- op( 500, fy, !).             % universal quantifier:  ![X]:
:- op( 500, fy, ?).             % existential quantifier:  ?[X]:
:- op( 500, xfy, :).            % quantifier separator
% Syntaxe d'entree : sequent turnstile
% Equivalence operator for sequents (bidirectional provability)
:- op(800, xfx, <>).
% =========================================================================
% OPERATEURS LATEX (sortie formatee)
% ATTENTION : Respecter exactement les espaces !
% =========================================================================
:- op( 500, fy, ' \\lnot ').     % negation
:- op(1000, xfy, ' \\land ').    % conjunction
:- op(1100, xfy, ' \\lor ').     % disjunction
:- op(1110, xfx, ' \\to ').      % conditional
:- op(1120, xfx, ' \\leftrightarrow ').  % biconditional
:- op( 500, fy, ' \\forall ').   % universal quantifier
:- op( 500, fy, ' \\exists ').   % existential quantifier
:- op( 500, xfy, ' ').           % espace pour quantificateurs
:- op(400, fx, ' \\bot ').      % falsity (#)
% Syntaxe LaTeX : sequent turnstile  
:- op(1150, xfx, ' \\vdash ').
% =========================================================================
% DOCUMENTATION DES OPERATEURS
% =========================================================================

% Priorites (ordre croissant) :
% 500  : ~, !, ?, :
% 1000 : &
% 1100 : |
% 1110 : =>
% 1120 : <=>
% 1200 : f (?)

% Associativite :
% fy  : prefixe, associatif a droite (ex: ~ ~p)
% xfy : infixe, associatif a droite (ex: p & q & r)
% xfx : infixe, non associatif (ex: p <=> q)
% fx  : prefixe, non associatif (ex: f)

% Usage dans les modules :
% :- [operators].  % Inclure en debut de fichier
% =========================================================================
% OPERATEURS POUR SEQUENTS - AJOUT
% =========================================================================
% =========================================================================
% UNIFIED OPTIMIZED DRIVER: PATTERN DETECTION + 2-PASS STRATEGY
% Version with native G4 sequent syntax [Premises] > [Conclusion]
% =========================================================================
:- use_module(library(lists)).
:- use_module(library(statistics)).
:- use_module(library(terms)).
% =========================================================================
% STARTUP BANNER
% =========================================================================
% Désactiver le banner automatique de SWI-Prolog
:- set_prolog_flag(verbose, silent).

% Puis ton initialisation
:- initialization(show_banner).

show_banner :-
    write('Welcome to SWI-Prolog (32 bits, version 9.3.34-20-g3517bc35f)'),nl,
    write('SWI-Prolog comes with ABSOLUTELY NO WARRANTY. This is free software.'),nl,
    write('For legal details and online help, see https://www.swi-prolog.org'),nl,nl,

    write('*****************************************************************'), nl,
    write('*                   G4-mic F.O.L. PROVER  -  1.0                *'), nl,
    write('*         (mic: minimal, intuitionistic and classical logic)    *'), nl,
    write('*****************************************************************'), nl,
    nl,
    write('Write below: '),nl,
    write('  help. and press Enter to get help'), nl,
    write('  examples. and press Enter to see examples'),nl.
% =========================================================================
% ITERATION LIMITS CONFIGURATION
% =========================================================================

logic_iteration_limit(constructive, 3).
logic_iteration_limit(classical, 15).
logic_iteration_limit(minimal, 3).
logic_iteration_limit(intuitionistic, 5).
logic_iteration_limit(fol, 15).

% =========================================================================
% UTILITY for/3
% =========================================================================

for(I, M, N) :- M =< N, I = M.
for(I, M, N) :- M < N, M1 is M+1, for(I, M1, N).

% =========================================================================
% DETECTION THEOREME vs SEQUENT (simplifie)
% =========================================================================

:- dynamic current_proof_sequent/1.
:- dynamic premise_list/1.

% =========================================================================
% OPTIMIZED CLASSICAL PATTERN DETECTION
% =========================================================================

% normalize_formula/2: Apply efficiency-improving transformations
normalize_formula(Formula, Normalized) :-
    normalize_double_negations(Formula, F1),
    normalize_biconditional_order(F1, Normalized).

% normalize_double_negations/2: Simplify ~~A patterns in safe contexts
normalize_double_negations(((A => #) => #), A) :- 
    A \= (_ => #), !.
normalize_double_negations(A & B, NA & NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(A | B, NA | NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(A => B, NA => NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(A <=> B, NA <=> NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(![X]:A, ![X]:NA) :- !,
    normalize_double_negations(A, NA).
normalize_double_negations(?[X]:A, ?[X]:NA) :- !,
    normalize_double_negations(A, NA).
normalize_double_negations(F, F).

% normalize_biconditional_order/2: Order biconditionals by complexity
normalize_biconditional_order(A <=> B, B <=> A) :-
    formula_complexity(A, CA),
    formula_complexity(B, CB),
    CB < CA, !.
normalize_biconditional_order(A <=> B, NA <=> NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(A & B, NA & NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(A | B, NA | NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(A => B, NA => NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(![X]:A, ![X]:NA) :- !,
    normalize_biconditional_order(A, NA).
normalize_biconditional_order(?[X]:A, ?[X]:NA) :- !,
    normalize_biconditional_order(A, NA).
normalize_biconditional_order(F, F).

% formula_complexity/2: Heuristic complexity measure
formula_complexity((A => #), C) :- !, 
    formula_complexity(A, CA), 
    C is CA + 2.
formula_complexity(A => B, C) :- !, 
    formula_complexity(A, CA), 
    formula_complexity(B, CB), 
    C is CA + CB + 3.
formula_complexity(A & B, C) :- !, 
    formula_complexity(A, CA), 
    formula_complexity(B, CB), 
    C is CA + CB + 2.
formula_complexity(A | B, C) :- !, 
    formula_complexity(A, CA), 
    formula_complexity(B, CB), 
    C is CA + CB + 2.
formula_complexity(A <=> B, C) :- !, 
    formula_complexity(A, CA), 
    formula_complexity(B, CB), 
    C is CA + CB + 4.
formula_complexity(![_]:A, C) :- !, 
    formula_complexity(A, CA), 
    C is CA + 5.
formula_complexity(?[_]:A, C) :- !, 
    formula_complexity(A, CA), 
    C is CA + 5.
formula_complexity(_, 1).

% =========================================================================
% CLASSICAL PATTERN DETECTION (Core)
% =========================================================================

is_classical_pattern(Formula) :-
    (   is_fol_structural_pattern(Formula) ->
        !
    ;   contains_classical_pattern(Formula)
    ).

contains_classical_pattern(Formula) :-
    is_basic_classical_pattern(Formula), !.
contains_classical_pattern(Formula) :-
    binary_connective(Formula, Left, Right),
    (contains_classical_pattern(Left) ; contains_classical_pattern(Right)), !.
contains_classical_pattern(![_-_]:A) :-
    contains_classical_pattern(A), !.
contains_classical_pattern(?[_-_]:A) :-
    contains_classical_pattern(A), !.

binary_connective(A & B, A, B).
binary_connective(A | B, A, B).
binary_connective(A => B, A, B).
binary_connective(A <=> B, A, B).

% BASIC CLASSICAL PATTERNS
is_basic_classical_pattern(A | (A => #)) :- !.
is_basic_classical_pattern((A => #) | A) :- !.
is_basic_classical_pattern(((A => #) => #) => A) :- 
    A \= (_ => #), !.
is_basic_classical_pattern(((A => _B) => A) => A) :- !.
is_basic_classical_pattern((A => B) => ((A => #) | B)) :- !.
is_basic_classical_pattern((A => B) => (B | (A => #))) :- !.
is_basic_classical_pattern((A => B) | (B => A)) :- !.
is_basic_classical_pattern(((B => #) => (A => #)) => (A => B)) :- !.
is_basic_classical_pattern((A => B) => ((B => #) => (A => #))) :- !.
is_basic_classical_pattern(((A => B) => #) => (A & (B => #))) :- !.
is_basic_classical_pattern(((A & B) => #) => ((A => #) | (B => #))) :- !.
is_basic_classical_pattern((((A => #) => B) & (A => B)) => B) :- !.
is_basic_classical_pattern(((A => B) & ((A => #) => B)) => B) :- !.

% FOL STRUCTURAL PATTERNS
is_fol_structural_pattern(((![_-_]:_ => _) => (?[_-_]:(_ => _)))) :- !.
is_fol_structural_pattern(?[_-_]:(_ => ![_-_]:_)) :- !.
is_fol_structural_pattern((![_-_]:(_ | _)) => (_ | ![_-_]:_)) :- !.
is_fol_structural_pattern((![_-_]:(_ | _)) => (![_-_]:_ | _)) :- !.
is_fol_structural_pattern((_) => ?[_-_]:(_ & ![_-_]:(_ | _))) :- !.

% =========================================================================
% MAIN INTERFACE: prove/1
% =========================================================================

% NOUVEAU : Detection automatique pour sequents avec premisses
prove(G > D) :-
    G \= [],  % Premisses non vides = SEQUENT
    !,
     %  VALIDATION : Verifier les premisses et la conclusion
    validate_sequent_formulas(G, D),
    statistics(runtime, [_T0|_]),
    write('------------------------------------------'), nl,
    write('G4 PROOF FOR SEQUENT: '),
    write_sequent_compact(G, D), nl,
    write('------------------------------------------'), nl,
    write('MODE: Sequent '), nl,
    nl,
    
    % Stocker les premisses pour l'affichage
    retractall(premise_list(_)),
    assertz(premise_list(G)),
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(G > D)),
    
    % Preparer les formules
    copy_term((G > D), (GCopy > DCopy)),
    prepare_sequent_formulas(GCopy, DCopy, PrepG, PrepD),
    
    % Detecter pattern classique dans la conclusion
    ( DCopy = [SingleGoal], is_classical_pattern(SingleGoal) ->
        write('=== CLASSICAL PATTERN DETECTED ==='), nl,
        write('    -> Using classical logic'), nl,
        time(provable_at_level(PrepG > PrepD, classical, Proof)),
        Logic = classical,
        OutputProof = Proof
    ;
        write('=== PHASE 1: Trying Minimal -> Intuitionistic -> Classical ==='), nl,
        ( time(provable_at_level(PrepG > PrepD, minimal, Proof)) ->
            write('   Constructive proof found in MINIMAL LOGIC '), nl,
            Logic = minimal,
            OutputProof = Proof
        ; time(provable_at_level(PrepG > PrepD, constructive, Proof)) ->
            write('   Constructive proof found'), nl,
            ( proof_uses_lbot(Proof) ->
                write('  Constructive proof found in INTUITIONISTIC LOGIC'), nl,
                Logic = intuitionistic
            ),
            OutputProof = Proof
        ;
            write('    Constructive logic failed'), nl,
            write('=== TRYING CLASSICAL LOGIC ==='), nl,
            time(provable_at_level(PrepG > PrepD, classical, Proof)),
            write('    Proof found in CLASSICAL LOGIC '), nl,
            Logic = classical,
            OutputProof = Proof
        )
    ),
    output_proof_results(OutputProof, Logic, G > D, sequent).

% Biconditionals - REGROUPES PAR TYPE
prove(Left <=> Right) :- !,
         % VALIDATION : Verifier les deux directions
    validate_and_warn(Left, _),
    validate_and_warn(Right, _),
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(Left => Right)),
    time((decide_silent(Left => Right, Proof1, Logic1))),
    
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(Right => Left)),
    time((decide_silent(Right => Left, Proof2, Logic2))),
    
    nl,
    write('=== BICONDITIONAL: Proving both directions ==='), nl,
    output_logic_label(Logic1), nl, nl,
  %  write('    '), portray_clause(Proof1), nl,nl,
    output_logic_label(Logic2), nl, nl,
  % write('    '), portray_clause(Proof2), nl,nl,
  % write('Q.E.D.'), nl, nl,
    
    % SEQUENT CALCULUS - BOTH DIRECTIONS
    write('- Sequent Calculus -'), nl, nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof1, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof2, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('Q.E.D.'), nl, nl,
    
    % TREE STYLE - BOTH DIRECTIONS
    write('- Natural Deduction -'), nl,
    write('a) Tree Style:'), nl, nl,
    render_nd_tree_proof(Proof1), nl, nl,
    render_nd_tree_proof(Proof2), nl, nl,
    write('Q.E.D.'), nl, nl,
    
    % TREE STYLE - BOTH DIRECTIONS
    write('b) Flag Style:'), nl, nl,
    write('\\begin{fitch}'), nl,
    g4_to_fitch_theorem(Proof1),
    write('\\end{fitch}'), nl, nl,
    write('\\begin{fitch}'), nl,
    g4_to_fitch_theorem(Proof2),
    write('\\end{fitch}'), nl, nl,
    write('Q.E.D.'), nl, nl,
    
    write('This biconditional is valid:'), nl,
    write('- Direction 1 ('), write(Left => Right), write(')'),  
    write(' is valid in '), write(Logic1), write(' logic'), nl,
    write('- Direction 2 ('), write(Right => Left), write(')'),
    write(' is valid in '), write(Logic2), write(' logic.'), nl,
    !.


% Equivalence de sequents: [A] <> [B] prouve [A] > [B] ET [B] > [A]
prove([Left] <> [Right]) :- !,
          % VALIDATION : Verifier les deux formules
    validate_and_warn(Left, _),
    validate_and_warn(Right, _),
    retractall(current_proof_sequent(_)),
    % Direction 1: Left > Right
    assertz(current_proof_sequent([Left] > [Right])),
    time((prove_sequent_silent([Left] > [Right], Proof1, Logic1))),   
    % Direction 2: Right > Left
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Right] > [Left])),
    time((prove_sequent_silent([Right] > [Left], Proof2, Logic2))),
    nl,
    write('=== SEQUENT EQUIVALENCE: Proving both directions ==='), nl,
    output_logic_label(Logic1), nl, nl,
  %  write('    '), portray_clause(Proof1), nl, nl,
    output_logic_label(Logic2), nl, nl,
  %  write('    '), portray_clause(Proof2), nl, nl,
  %  write('Q.E.D.'), nl, nl,
    
    % SEQUENT CALCULUS - BOTH DIRECTIONS
    write('- Sequent Calculus -'), nl, nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof1, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof2, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('Q.E.D.'), nl, nl,

    % TREE STYLE - BOTH DIRECTIONS
    write('- Natural Deduction -'), nl,
    write('a) Tree Style:'), nl, nl,
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Left] > [Right])),
    retractall(premise_list(_)),
    assertz(premise_list([Left])),
    render_nd_tree_proof(Proof1), nl, nl,
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Right] > [Left])),
    retractall(premise_list(_)),
    assertz(premise_list([Right])),
    render_nd_tree_proof(Proof2), nl, nl,
    write('Q.E.D.'), nl, nl,

    % FITCH STYLE - BOTH DIRECTIONS
    write('b) Flag Style:'), nl, nl,
    write('\\begin{fitch}'), nl,
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Left] > [Right])),
    retractall(premise_list(_)),
    assertz(premise_list([Left])),
    g4_to_fitch_sequent(Proof1, [Left] > [Right]),
    write('\\end{fitch}'), nl, nl,
    write('\\begin{fitch}'), nl,
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Right] > [Left])),
    retractall(premise_list(_)),
    assertz(premise_list([Right])),
    g4_to_fitch_sequent(Proof2, [Right] > [Left]),
    write('\\end{fitch}'), nl, nl,
    write('Q.E.D.'), nl, nl,
       
    write('This sequent equivalence is valid:'), nl,
    write('- Direction 1 ('), write(Left), write(' |- '), write(Right), write(')'),  
    write(' is valid in '), write(Logic1), write(' logic'), nl,
    write('- Direction 2 ('), write(Right), write(' |- '), write(Left), write(')'),
    write(' is valid in '), write(Logic2), write(' logic.'), nl,
    !.

% Theorems (original logic)
prove(Formula) :-
         % VALIDATION : Verifier la formule
    validate_and_warn(Formula, _ValidatedFormula),
    statistics(runtime, [_T0|_]),
    write('------------------------------------------'), nl,
    write('G4 PROOF FOR: '), write(Formula), nl,
    write('------------------------------------------'), nl,  
    write('MODE: Theorem '), nl,
    nl,
    
    retractall(premise_list(_)),
    retractall(current_proof_sequent(_)),
    
    copy_term(Formula, FormulaCopy),
    prepare(FormulaCopy, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1, F2),
    
    (   F2 = ((A => #) => #), A \= (_ => #)  ->
        write('=== DOUBLE NEGATION DETECTED ==='), nl,
        write('    -> Trying constructive first'), nl,
        write('=== TRYING CONSTRUCTIVE LOGIC ==='), nl,
        ( time(provable_at_level([] > [F2], constructive, Proof)) ->
            write('   Constructive proof found'), nl,
            ( time(provable_at_level([] > [F2], minimal, _)) ->
                write('  Constructive proof found in MINIMAL LOGIC'), nl,
                Logic = minimal,
                OutputProof = Proof
            ;
                ( proof_uses_lbot(Proof) ->
                    write('  Constructive proof found in INTUITIONISTIC LOGIC'), nl,
                    Logic = intuitionistic,
                    OutputProof = Proof
                )
            )
        ;
            write('    Constructive logic failed'), nl,
            write('=== FALLBACK: CLASSICAL LOGIC ==='), nl,
            time(provable_at_level([] > [F2], classical, Proof)),
            write('   Classical proof found'), nl,
            Logic = classical,
            OutputProof = Proof
        )
    ; is_classical_pattern(F2) ->
        write('=== CLASSICAL PATTERN DETECTED ==='), nl,
        write('    -> Skipping constructive logic'), nl,
        write('=== TRYING CLASSICAL LOGIC ==='), nl,
        time(provable_at_level([] > [F2], classical, Proof)),
        write('   Classical proof found'), nl,
        Logic = classical,
        OutputProof = Proof
    ;
        write('=== PHASE 1: Trying Minimal -> Intuitionistic -> Classical ==='), nl,
        ( time(provable_at_level([] > [F2], minimal, Proof)) ->
            write('   Proof found in MINIMAL LOGIC'), nl,
            Logic = minimal,
            OutputProof = Proof
        ; time(provable_at_level([] > [F2], constructive, Proof)) ->
            write('   Constructive proof found'), nl,
            ( proof_uses_lbot(Proof) ->
                write('  -> Uses explosion explosion rule - Proof found in INTUITIONISTIC LOGIC'), nl,
                Logic = intuitionistic,
                OutputProof = Proof
            ;
                write('  -> No explosion -> INTUITIONISTIC'), nl,
                Logic = intuitionistic,
                OutputProof = Proof
            )
        ;
            write('   Constructive logic failed'), nl,
            write('=== TRYING CLASSICAL LOGIC ==='), nl,
            time(provable_at_level([] > [F2], classical, Proof)),
            write('  Proof found in Classical logic'), nl,
            Logic = classical,
            OutputProof = Proof
        )
    ),
    output_proof_results(OutputProof, Logic, Formula, theorem).

% =========================================================================
% HELPERS
% =========================================================================

% Preparer une liste de formules
prepare_sequent_formulas(GIn, DIn, GOut, DOut) :-
    maplist(prepare_and_subst, GIn, GOut),
    maplist(prepare_and_subst, DIn, DOut).

prepare_and_subst(F, FOut) :-
    prepare(F, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1, FOut).

% Affichage compact d'un sequent
write_sequent_compact([], [D]) :- !, write(' |- '), write(D).
write_sequent_compact([G], [D]) :- !, write(G), write(' |- '), write(D).
write_sequent_compact(G, [D]) :-
    write_list_compact(G),
    write(' |- '),
    write(D).

write_list_compact([X]) :- !, write(X).
write_list_compact([X|Xs]) :- write(X), write(', '), write_list_compact(Xs).

% =========================================================================
% VALIDATION DES FORMULES ET SEQUENTS
% =========================================================================

% Valider un sequent (premisses + conclusions)
validate_sequent_formulas(G, D) :-
    % Valider toutes les premisses
    forall(member(Premise, G), validate_and_warn(Premise, _)),
    % Valider toutes les conclusions
    forall(member(Conclusion, D), validate_and_warn(Conclusion, _)).

% =========================================================================
% OUTPUT WITH MODE DETECTION
% =========================================================================

output_proof_results(Proof, LogicType, OriginalFormula, Mode) :-
    extract_formula_from_proof(Proof, Formula),
    detect_and_set_logic_level(Formula),
    output_logic_label(LogicType),
  %  write('Prolog terms:'), nl, nl,
  %  write('    '),
    ( catch(
          (copy_term(Proof, ProofCopy),
           numbervars(ProofCopy, 0, _),
         %  portray_clause(ProofCopy),
           nl, nl),
          error(cyclic_term, _),
          (write('%% WARNING: Cannot represent proof term due to cyclic_term.'), nl, nl)
      ) -> true ; true ),
   % write('Q.E.D.'), nl, nl,
    write('- Sequent Calculus -'), nl,nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('Q.E.D.'), nl, nl,
    write('- Natural Deduction -'), nl,
     write('a) Tree Style:'), nl, nl,
    render_nd_tree_proof(Proof),nl,nl,
    write('Q.E.D.'), nl, nl,
    write('b) Flag Style:'), nl, nl,
    write('\\begin{fitch}'), nl,
    ( Mode = sequent ->
        g4_to_fitch_sequent(Proof, OriginalFormula)
    ;
        g4_to_fitch_theorem(Proof)
    ),
    write('\\end{fitch}'), nl, nl,
    write('Q.E.D.'), nl, nl,
    !.

% =========================================================================
% SILENT VERSIONS (for internal use)
% =========================================================================

decide_silent(Formula, Proof, Logic) :-
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(Formula)),
    
    copy_term(Formula, FormulaCopy),
    prepare(FormulaCopy, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1,F2),
    progressive_proof_silent(F2, Proof, Logic).

progressive_proof_silent(Formula, Proof, Logic) :-
    ( provable_at_level([] > [Formula], constructive, Proof) ->
        Logic = constructive
    ; provable_at_level([] > [Formula], classical, Proof) ->
        Logic = classical
    ).

% =========================================================================
% PROVABILITY AT A GIVEN LEVEL (simplifie)
% =========================================================================
provable_at_level(Sequent, constructive, P) :-
    !,
    logic_iteration_limit(constructive, MaxIter),
    for(I, 0, MaxIter),
    Sequent = (G > D),
    ( prove(G > D, [], I, 1, _, minimal, P) -> true    % <- Essayer minimal d'abord
    ; prove(G > D, [], I, 1, _, intuitionistic, P)     % <- Puis intuitionistic si echec
    ),
    !.

provable_at_level(Sequent, LogicLevel, P) :-
    logic_iteration_limit(LogicLevel, MaxIter),
    for(I, 0, MaxIter),
    Sequent = (G > D),
    prove(G > D, [], I, 1, _, LogicLevel, P),
    !.


provable_at_level(Sequent, constructive, P) :-
    !,
    logic_iteration_limit(constructive, MaxIter),
    for(I, 0, MaxIter),
    Sequent = (G > D),
    ( prove(G > D, [], I, 1, _, minimal, P) -> true    % <- Essayer minimal d'abord
    ; prove(G > D, [], I, 1, _, intuitionistic, P)     % <- Puis intuitionistic si echec
    ),
    !.

% =========================================================================
% DISPLAY HELPERS
% =========================================================================
% Helper: prove sequent silently (for <> operator)
prove_sequent_silent(Sequent, Proof, Logic) :-
    Sequent = (G > D),
    prepare_sequent_formulas(G, D, PrepG, PrepD),
    ( member(SingleGoal, PrepD), is_classical_pattern(SingleGoal) ->
        provable_at_level(PrepG > PrepD, classical, Proof),
        Logic = classical
    ; provable_at_level(PrepG > PrepD, minimal, Proof) ->
        Logic = minimal
    ; provable_at_level(PrepG > PrepD, constructive, Proof) ->
        ( proof_uses_lbot(Proof) -> Logic = intuitionistic ; Logic = intuitionistic )
    ;
        provable_at_level(PrepG > PrepD, classical, Proof),
        Logic = classical
    ).

output_logic_label(constructive) :-
    nl,
    write('G4 Proofs:'), nl, nl.
output_logic_label(minimal) :- 
    write('G4 proofs in minimal logic'), nl, nl.
output_logic_label(intuitionistic) :- 
    write('G4 proofs in intuitionistic logic'), nl, nl.
output_logic_label(classical) :- 
    write('G4+IP proofs in classical logic'), nl, nl.

proof_uses_lbot(lbot(_,_)) :- !.
proof_uses_lbot(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    proof_uses_lbot(Arg).

% =========================================================================
% MINIMAL INTERFACE decide/1
% =========================================================================

decide(Left <=> Right) :- !,
         %  VALIDATION
    validate_and_warn(Left, _),
    validate_and_warn(Right, _),
    time((
        decide_silent(Left => Right, _, _),
        decide_silent(Right => Left, _, _)
    )),
    !.

decide(Formula) :-
    copy_term(Formula, FormulaCopy),
    prepare(FormulaCopy, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1,F2),
    ( is_classical_pattern(F2) ->
        time(provable_at_level([] > [F2], classical, _))
    ;
        time(progressive_proof_silent(F2, _, _))
    ),
    !.

% decide/1 for sequents
decide(G > D) :-
    G \= [], !,
       %  VALIDATION
    validate_sequent_formulas(G, D),
    copy_term((G > D), (GCopy > DCopy)),
    prepare_sequent_formulas(GCopy, DCopy, PrepG, PrepD),
    
    ( DCopy = [SingleGoal], is_classical_pattern(SingleGoal) ->
        time(provable_at_level(PrepG > PrepD, classical, _))
    ;
        ( time(provable_at_level(PrepG > PrepD, minimal, _)) ->
            true
        ; time(provable_at_level(PrepG > PrepD, constructive, _)) ->
            true
        ;
            time(provable_at_level(PrepG > PrepD, classical, _))
        )
    ),
    !.

% Equivalence pour decide
decide([Left] <> [Right]) :- !,
         %  VALIDATION
    validate_and_warn(Left, _),
    validate_and_warn(Right, _),
    time((
        decide([Left] > [Right]),
        decide([Right] > [Left])
    )),
    !.
 
% =========================================================================
% HELP SYSTEM
% =========================================================================

help :-
    nl,
    write('*****************************************************************'), nl,
    write('*                      G4 PROVER GUIDE                          *'), nl,
    write('*****************************************************************'), nl,
    write('## MAIN COMMANDS '), nl,
    write('  prove(Formula).            - shows the proofs of Formula'), nl,
    write('  decide(Formula).           - says either true or false'), nl,
    write('## SYNTAX EXAMPLES '), nl,
    write('  THEOREMS:'), nl,
    write('    prove(p => p).                    - Identity'), nl,
    write('    prove((p & q) => p).              - Conjunction elimination'), nl,
    write('  SEQUENTS (syntax of G4 prover):'), nl,
    write('    prove([p] > [p]).                 - Sequent: P |- P '), nl,
    write('    prove([p, q] > [p & q]).          - Sequent: P , Q |- P & Q '), nl,
    write('    prove([p => q, p] > [q]).         - Modus Ponens in sequent form'), nl,
    write('  BICONDITIONALS:'), nl,
    write('    prove(p <=> ~ ~ p).                - Biconditional of Double Negation '), nl,
    write('    prove([p] <> [~ ~ p]).             - Bi-implication of Double Negation (sequents)'), nl,
    write('## COMMON MISTAKES '), nl,
    write('   [p] => [p]          - WRONG (use > for sequents)'), nl,
    write('   [p] > [p]           - CORRECT (sequent syntax)'), nl,
    write('   p > q               - WRONG (use => for conditional)'), nl,
    write('   p => q              - CORRECT (conditional)'), nl,
    write('   x <=> y in FOL      - WRONG (use = for equality)'), nl,
    write('   x = y in FOL        - CORRECT (equality)'), nl,
    write('## LOGICAL OPERATORS '), nl,
    write('  ~ A , (A & B) , (A | B) , (A => B) , (A <=> B) ,  # , ![x]:A ,  ?[x]:A').

examples :-
    nl,
    write('*****************************************************************'), nl,
    write('*                     EXAMPLES                                  *'), nl,
    write('*****************************************************************'), nl,
    nl,
    write('  % Identity theorem'), nl,
    write('  ?- prove(p => p).'), nl,
    write('  % Sequent with single premiss'), nl,
    write('  ?- prove([p] > [p]).'), nl,
    write('  % Sequent with multiple premisses'), nl,
    write('  ?- prove([p, q] > [p & q]).'), nl,
    write('  % Sequent: modus ponens'), nl,
    write('  ?- prove([p => q, p] > [q]).'), nl,
    write('  % Law of Excluded Middle (classical)'), nl,
    write('  ?- prove(~ p | p).'), nl,
    write('  % Drinker Paradox (classical)'), nl,
    write('  ?- prove(?[y]:(d(y) => ![x]:d(x))).'), nl,
    nl.

% ============================================
% DRIVER - Test Suite Runner with Timer
% ============================================

%! run_all_test_files
%  Execute l'integralite de la suite de tests avec mesure du temps
%  Inclut : tests unitaires, sequents FOL/Prop, Pelletier
run_all_test_files :- 
    get_time(StartTime),
    writeln(''),
    writeln('##############################################'),
    writeln('#   START OF THE COMPLETE SERIES OF TESTS    #'),
    writeln('##############################################'),
    format('Start : ~w~n~n', [StartTime]),
    
    safe_run(run_all_tests, ' FOL Theorems '),
    safe_run(run_prop_seq, 'Propositional sequents'),
    safe_run(run_fol_seq, 'FOL Valid Sequents'),
    safe_run(run_pelletier, 'Pelletier Problems'),
    
    get_time(EndTime),
    ElapsedTime is EndTime - StartTime,
    
    writeln(''),
    writeln('##############################################'),
    writeln('#    END OF THE COMPLETE SERIES OF TESTS     #'),
    writeln('##############################################'),
    format_execution_time(ElapsedTime),
    writeln('').

%! safe_run(+Goal, +Name)
%  Execute un predicat de test avec gestion d'erreurs et chronometre
safe_run(Goal, Name) :-
    format('~n--- ~w ---~n', [Name]),
    get_time(Start),
    catch(
        (call(Goal) -> 
            (get_time(End), 
             Duration is End - Start,
             format('? ~w : SUCCES (~2f secondes)~n', [Name, Duration])) 
        ; 
            (get_time(End), 
             Duration is End - Start,
             format('? ~w : ECHEC (~2f secondes)~n', [Name, Duration]))
        ),
        Error,
        (get_time(End), 
         Duration is End - Start,
         format('? ~w : ERREUR - ~w (~2f secondes)~n', [Name, Error, Duration]))
    ).

%! format_execution_time(+Seconds)
%  Affiche le temps d'execution dans un format lisible
format_execution_time(Seconds) :-
    Seconds < 60,
    !,
    format('Temps total d\'execution : ~2f secondes~n', [Seconds]).
format_execution_time(Seconds) :-
    Seconds < 3600,
    !,
    Minutes is floor(Seconds / 60),
    RemainingSeconds is Seconds - (Minutes * 60),
    format('Temps total d\'execution : ~d min ~2f sec~n', [Minutes, RemainingSeconds]).
format_execution_time(Seconds) :-
    Hours is floor(Seconds / 3600),
    RemainingMinutes is floor((Seconds - (Hours * 3600)) / 60),
    RemainingSeconds is Seconds - (Hours * 3600) - (RemainingMinutes * 60),
    format('Temps total d\'execution : ~d h ~d min ~2f sec~n', [Hours, RemainingMinutes, RemainingSeconds]).
% =========================================================================
% END OF DRIVER
% =========================================================================
% =========================================================================
% TRADUCTION DU BICONDITIONNELLE INTERNE
% A <=> B devient (A => B) & (B => A)
% =========================================================================

subst_bicond(A <=> B, (A1 => B1) & (B1 => A1)) :-
    !,
    subst_bicond(A, A1),
    subst_bicond(B, B1).

% Quantificateurs : passer recursivement dans le corps
subst_bicond(![Z-X]:A, ![Z-X]:A1) :-
        !,
        subst_bicond(A, A1).

subst_bicond(?[Z-X]:A, ?[Z-X]:A1) :-
        !,
        subst_bicond(A, A1).

% Connecteurs propositionnels
subst_bicond(A & B, A1 & B1) :-
        !,
        subst_bicond(A, A1),
        subst_bicond(B, B1).

subst_bicond(A | B, A1 | B1) :-
        !,
        subst_bicond(A, A1),
        subst_bicond(B, B1).

subst_bicond(A => B, A1 => B1) :-
        !,
        subst_bicond(A, A1),
        subst_bicond(B, B1).

subst_bicond(~A, ~A1) :-
        !,
        subst_bicond(A, A1).

% Cas de base : formules atomiques
subst_bicond(A, A).

% =========================================================================
% SUBSTITUTION DE LA NEGATION (pretraitement)
% =========================================================================
% Double negation
subst_neg(~ ~A, ((A1 => #) => #)) :-
        !,
        subst_neg(A, A1).

% Negation simple
subst_neg(~A, (A1 => #)) :-
        !,
        subst_neg(A, A1).


subst_neg(![Z-X]:A, ![Z-X]:A1) :-
        !,
        subst_neg(A, A1).

subst_neg(?[Z-X]:A, ?[Z-X]:A1) :-
        !,
        subst_neg(A, A1).

% Conjonction
subst_neg(A & B, A1 & B1) :-
        !,
        subst_neg(A, A1),
        subst_neg(B, B1).

% Disjonction
subst_neg(A | B, A1 | B1) :-
        !,
        subst_neg(A, A1),
        subst_neg(B, B1).

% Implication
subst_neg(A => B, A1 => B1) :-
        !,
        subst_neg(A, A1),
        subst_neg(B, B1).

% Biconditional
subst_neg(A <=> B, A1 <=> B1) :-
    !,
    subst_neg(A, A1),
    subst_neg(B, B1).

% Bacis case
subst_neg(A, A).
% =========================================================================
% G4 FOL Prover with equality 
% TPTP-version
% =========================================================================
% prove/7 - 
% prove(Sequent, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, Proof)
% LogicLevel: minimal | intuitionistic | classical
%==========================================================================
% AXIOMS
%=========================================================================
% O.0 Ax 
prove(G > D, _, _, J, J, _, ax(G>D, ax)) :-
    member(A, G),
    A\=(_&_),
    A\=(_|_),
    A\=(_=>_),
    A\=(!_),
    A\=(?_),
    D = [B],
    unify_with_occurs_check(A, B).
% 0.1 L-bot
prove(G>D, _, _, J, J, LogicLevel, lbot(G>D, #)) :-
    member(LogicLevel, [intuitionistic, classical]),
    member(#, G), !.
% =========================================================================
%  PROPOSITIONAL RULES
% =========================================================================
% 1. L&
prove(G>D, FV, I, J, K, LogicLevel, land(G>D,P)) :-
    select((A&B),G,G1), !,
    prove([A,B|G1]>D, FV, I, J, K, LogicLevel, P).
% 2. L0->  
prove(G>D, FV, I, J, K, LogicLevel, l0cond(G>D,P)) :-
    select((A=>B),G,G1),
    member(A,G1), !,
    prove([B|G1]>D, FV, I, J, K, LogicLevel, P).
% 2. L&->
prove(G>D, FV, I, J, K, LogicLevel, landto(G>D,P)) :-
    select(((A&B)=>C),G,G1), !,
    prove([(A=>(B => C))|G1]>D, FV, I, J, K, LogicLevel, P).
% 3. TNE : Odd Negation Elimination
prove(G>D, FV, I, J, K, LogicLevel, tne(G>D, P)) :-
    D = [(A => B)],  % Goal: not-A
    % Search in G for a formula with more negations
    member(LongNeg, G),
    % Verify that LongNeg = not^n(not-A) with n >= 2 (so total >= 3)
    is_nested_negation(LongNeg, A => B, Depth),
    Depth >= 2,  % At least 2 more negations than the goal
    !,
    prove([A|G]>[B], FV, I, J, K, LogicLevel, P).
% 7. IP (Indirect Proof - THE classical law). 
prove(G>D, FV, I, J, K, classical, ip(G>D, P)) :-
    D = [A],  % Any goal A (not just bottom)
    A \= #,   % Not already bottom
    \+ member((A => #), G),  % not-A not already in context
    I > 0,
    prove([(A => #)|G]>[#], FV, I, J, K, classical, P).
% 4. Lv-> (OPTIMIZED)
prove(G>D, FV, I, J, K, LogicLevel, lorto(G>D,P)) :-
    select(((A|B)=>C),G,G1), !,
    % Check which disjuncts are present
    ( member(A, G1), member(B, G1) ->
        % Both present: keep both (rare case)
        prove([A=>C,B=>C|G1]>D, FV, I, J, K, LogicLevel, P)
    ; member(A, G1) ->
        % Only A present: keep only A=>C
        prove([A=>C|G1]>D, FV, I, J, K, LogicLevel, P)
    ; member(B, G1) ->
        % Only B present: keep only B=>C
        prove([B=>C|G1]>D, FV, I, J, K, LogicLevel, P)
    ;
        % Neither present: keep both (default behavior)
        prove([A=>C,B=>C|G1]>D, FV, I, J, K, LogicLevel, P)
    ).
% 5. Lv (fallback for all logics including minimal)
prove(G>D, FV, I, J, K, LogicLevel, lor(G>D, P1,P2)) :-
    select((A|B),G,G1), !,
    prove([A|G1]>D, FV, I, J, J1, LogicLevel, P1),
    prove([B|G1]>D, FV, I, J1, K, LogicLevel, P2).
% 13. R-forall 
prove(G > D, FV, I, J, K, LogicLevel, rall(G>D, P)) :-
    select((![_Z-X]:A), D, D1), !,
    copy_term((X:A,FV), (f_sk(J,FV):A1,FV)),
    J1 is J+1,
    prove(G > [A1|D1], FV, I, J1, K, LogicLevel, P).
% 14. L-forall 
prove(G > D, FV, I, J, K, LogicLevel, lall(G>D, P)) :-
    member((![_Z-X]:A), G),
    length(FV, Len), Len < I,  
    copy_term((X:A,FV), (Y:A1,FV)),
    prove([A1|G] > D, [Y|FV], I, J, K, LogicLevel, P), !.
% 8. R-> 
prove(G>D, FV, I, J, K, LogicLevel, rcond(G>D,P)) :-
    D = [A=>B], !,
    prove([A|G]>[B], FV, I, J, K, LogicLevel, P).
% 6. L->-> 
prove(G>D, FV, I, J, K, LogicLevel, ltoto(G>D,P1,P2)) :-
    select(((A=>B)=>C),G,G1), !,
    prove([A,(B=>C)|G1]>[B], FV, I, J, _J1, LogicLevel, P1),
    prove([C|G1]> D, FV, I, _K1, K, LogicLevel, P2).
% 9 LvExists  (Quantification Rule Exception: must be *before* Rv)
prove(G>D, FV, I, J, K, LogicLevel, lex_lor(G>D, P1, P2)) :-
    select((?[_Z-X]:(A|B)), G, G1), !,
    copy_term((X:(A|B),FV), (f_sk(J,FV):(A1|B1),FV)),
    J1 is J+1,
    prove([A1|G1]>D, FV, I, J1, J2, LogicLevel, P1),
    prove([B1|G1]>D, FV, I, J2, K, LogicLevel, P2).
% 10. R? 
prove(G>D, FV, I, J, K, LogicLevel, ror(G>D, P)) :-
    D = [(A|B)], !,
    (   prove(G>[A], FV, I, J, K, LogicLevel, P)
    ;   prove(G>[B], FV, I, J, K, LogicLevel, P)
    ).
% 11. R-and : Right conjunction
prove(G>D, FV, I, J, K, LogicLevel, rand(G>D,P1,P2)) :-
    D = [(A&B)], !,
    prove(G>[A], FV, I, J, J1, LogicLevel, P1),
    prove(G>[B], FV, I, J1, K, LogicLevel, P2).
 % 12. L-exists 
prove(G > D, FV, I, J, K, LogicLevel, lex(G>D, P)) :-
    select((?[_Z-X]:A), G, G1), !,
    copy_term((X:A,FV), (f_sk(J,FV):A1,FV)),
    J1 is J+1,
    prove([A1|G1] > D, FV, I, J1, K, LogicLevel, P).
% 15. R-exists 
prove(G > D, FV, I, J, K, LogicLevel, rex(G>D, P)) :-
    select((?[_Z-X]:A), D, D1), !,
    length(FV, Len), Len < I,  
    copy_term((X:A,FV), (Y:A1,FV)),
    prove(G > [A1|D1], [Y|FV], I, J, K, LogicLevel, P), !.
% 16. CQ_c - Classical rule
prove(G>D, FV, I, J, K, classical, cq_c(G>D,P)) :-
    select((![Z-X]:A) => B, G, G1),
    
    % Search for (exists?:?) => B in G1
    ( member((?[ZTarget-YTarget]:ATarget) => B, G1),
      % Compare (A => B) with ATarget
      \+ \+ ((A => B) = ATarget) ->
        % Unifiable: use YTarget
        prove([?[ZTarget-YTarget]:ATarget|G1]>D, FV, I, J, K, classical, P)
    ;
        % Otherwise: normal case with X
        prove([?[Z-X]:(A => B)|G1]>D, FV, I, J, K, classical, P)
    ).
% 17. CQ_m - Minimal rule (minimal and intuitionistic ONLY, last resort)
% IMPORTANT: EXCLUDED from classical logic (IP + standard rules suffice)
prove(G>D, FV, I, J, K, LogicLevel, cq_m(G>D,P)) :-
    member(LogicLevel, [minimal, intuitionistic]),
    select((?[Z-X]:A)=>B, G, G1),
    prove([![Z-X]:(A=>B)|G1]>D, FV, I, J, K, LogicLevel, P).
% =========================================================================
% EQUALITY RULES
% =========================================================================
% REFLEXIVITY: |- t = t
prove(_G > D, _, _, J, J, _, eq_refl(D)) :-
    D = [T = T],
    ground(T),  % <- Ajouter cette ligne
    !.
% SYMMETRY: t = u |- u = t  
prove(G > D, _, _, J, J, _, eq_sym(G>D)) :-
    D = [A = B],
    member(B = A, G),
    !.
% SIMPLE TRANSITIVITY: t = u, u = v |- t = v
prove(G > D, _, _, J, J, _, eq_trans(G>D)) :-
    D = [A = C],
    A \== C,
    (   (member(A = B, G), member(B = C, G))
    ;   (member(B = A, G), member(B = C, G))
    ;   (member(A = B, G), member(C = B, G))
    ;   (member(B = A, G), member(C = B, G))
    ),
    !.
% CHAINED TRANSITIVITY: a=b, b=c, c=d |- a=d
prove(G > D, _, _, J, J, _, eq_trans_chain(G>D)) :-
    D = [A = C],
    A \== C,
    \+ member(A = C, G),
    \+ member(C = A, G),
    find_equality_path(A, C, G, [A], _Path),
    !.
% CONGRUENCE: t = u |- f(t) = f(u)
prove(G > D, _, _, J, J, _, eq_cong(G>D)) :-
    D = [LHS = RHS],
    LHS =.. [F|ArgsL],
    RHS =.. [F|ArgsR],
    length(ArgsL, N),
    length(ArgsR, N),
    N > 0,
    find_diff_pos(ArgsL, ArgsR, _Pos, TermL, TermR),
    (member(TermL = TermR, G) ; member(TermR = TermL, G)),
    !.
% SUBSTITUTION IN EQUALITY: x=y, f(x)=z |- f(y)=z
prove(G > D, _, _, J, J, _, eq_subst_eq(G>D)) :-
    D = [Goal_LHS = Goal_RHS],
    member(Ctx_LHS = Ctx_RHS, G),
    Ctx_LHS \== Goal_LHS,
    member(X = Y, G),
    X \== Y,
    (
        (substitute_in_term(X, Y, Ctx_LHS, Goal_LHS), Ctx_RHS == Goal_RHS)
    ;   (substitute_in_term(Y, X, Ctx_LHS, Goal_LHS), Ctx_RHS == Goal_RHS)
    ;   (substitute_in_term(X, Y, Ctx_RHS, Goal_RHS), Ctx_LHS == Goal_LHS)
    ;   (substitute_in_term(Y, X, Ctx_RHS, Goal_RHS), Ctx_LHS == Goal_LHS)
    ),
    !.
% SUBSTITUTION (Leibniz): t = u, P(t) |- P(u)
prove(G > D, _, _, J, J, _, eq_subst(G>D)) :-
    D = [Goal],
    Goal \= (_ = _),
    Goal \= (_ => _),
    Goal \= (_ & _),
    Goal \= (_ | _),
    Goal \= (!_),
    Goal \= (?_),
    member(A = B, G),
    member(Pred, G),
    Pred \= (_ = _),
    Pred \= (_ => _),
    Pred \= (_ & _),
    Pred \= (_ | _),
    Pred =.. [PredName|Args],
    Goal =.. [PredName|GoalArgs],
    member_pos(A, Args, Pos),
    nth0(Pos, GoalArgs, B),
    !.
% =========================================================================
% HELPERS
% =========================================================================
% Helper: find position of an element
member_pos(X, [X|_], 0) :- !.
member_pos(X, [_|T], N) :-
    member_pos(X, T, N1),
    N is N1 + 1.

% Helper: substitute Old with New in Term
substitute_in_term(Old, New, Old, New) :- !.
substitute_in_term(Old, New, Term, Result) :-
    compound(Term),
    !,
    Term =.. [F|Args],
    maplist(substitute_in_term(Old, New), Args, NewArgs),
    Result =.. [F|NewArgs].
substitute_in_term(_, _, Term, Term).

% Helper: find position where two lists differ
find_diff_pos([X|_], [Y|_], 0, X, Y) :- X \= Y, !.
find_diff_pos([X|RestL], [X|RestR], Pos, TermL, TermR) :-
    find_diff_pos(RestL, RestR, Pos1, TermL, TermR),
    Pos is Pos1 + 1.

% Helper: find a path (with cycle detection)
find_equality_path(X, X, _, _, [X]) :- !.
find_equality_path(X, Z, Context, Visited, [X|Path]) :-
    (member(X = Y, Context) ; member(Y = X, Context)),
    Y \== X,
    \+ member(Y, Visited),
    find_equality_path(Y, Z, Context, [Y|Visited], Path).

% Helper: verify if Formula = not^n(Target) and return n
is_nested_negation(Target, Target, 0) :- !.
is_nested_negation((Inner => #), Target, N) :-
    is_nested_negation(Inner, Target, N1),
    N is N1 + 1.
% =========================================================================
% END of Prover
% =========================================================================
% =========================================================================
% G4 PRINTER SPECIALISE POUR BUSSPROOFS
% Rendu LaTeX optimise pour les regles G4 authentiques
% =========================================================================

% Directive pour eviter les warnings
:- discontiguous render_bussproofs/3.

% =========================================================================
% G4 rules 
% =========================================================================

% 1. Ax.
render_bussproofs(ax(Seq, _), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize $Ax.$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% 2. L0-> 
render_bussproofs(l0cond(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $ L0\\to$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 3. L&-> 
render_bussproofs(landto(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $ L\\land\\to$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

render_bussproofs(tne(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $ R \\to$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 4. L?-> : Disjonction vers implication
render_bussproofs(lorto(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $ L\\lor\\to$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.


% Lexists-v
render_bussproofs(lex_lor(Seq, P1, P2), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P1, VarCounter, Temp1),
    render_bussproofs(P2, Temp1, Temp2),
    write('\\RightLabel{\\scriptsize $ L\\exists\\lor$}'), nl,
    write('\\BinaryInfC{$'),
    render_sequent(Seq, Temp2, FinalCounter),
    write('$}'), nl.

% 5. L&
render_bussproofs(land(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $ L\\land$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 6. Lv 
render_bussproofs(lor(Seq, P1, P2), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P1, VarCounter, Temp1),
    render_bussproofs(P2, Temp1, Temp2),
    write('\\RightLabel{\\scriptsize $ L\\lor$}'), nl,
    write('\\BinaryInfC{$'),
    render_sequent(Seq, Temp2, FinalCounter),
    write('$}'), nl.

% 7. R->
render_bussproofs(rcond(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $ R\\to$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 8. Rv 
render_bussproofs(ror(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $ R\\lor$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 9. L->-> 
render_bussproofs(ltoto(Seq, P1, P2), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P1, VarCounter, Temp1),
    render_bussproofs(P2, Temp1, Temp2),
    write('\\RightLabel{\\scriptsize $ L\\to\\to$}'), nl,
    write('\\BinaryInfC{$'),
    render_sequent(Seq, Temp2, FinalCounter),
    write('$}'), nl.

% 10. R& 
render_bussproofs(rand(Seq, P1, P2), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P1, VarCounter, Temp1),
    render_bussproofs(P2, Temp1, Temp2),
    write('\\RightLabel{\\scriptsize $ R\\land$}'), nl,
    write('\\BinaryInfC{$'),
    render_sequent(Seq, Temp2, FinalCounter),
    write('$}'), nl.

% 11. Lbot
render_bussproofs(lbot(Seq, _), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize $ L\\bot$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% IP : Indirect proof (avec detection DNE_m)
render_bussproofs(ip(Seq, P), VarCounter, FinalCounter) :-
    !,
    Seq = (_ > [Goal]),
    render_bussproofs(P, VarCounter, TempCounter),
    ( Goal = (_ => #) ->
        write('\\RightLabel{\\scriptsize $ DNE_{m}$}'), nl
    ;
        write('\\RightLabel{\\scriptsize $ IP$}'), nl
    ),
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% =========================================================================
%  FOL QUANTIFICATION RULES
% =========================================================================

% 12. Rforall 
render_bussproofs(rall(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $ R\\forall$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 13. Lexists 
render_bussproofs(lex(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $ L\\exists$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 14. Rexists
render_bussproofs(rex(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $ R\\exists$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 15. Lforall
render_bussproofs(lall(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $L\\forall$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.


% CQ_c : Regle de conversion classique (?x:A => B) => ?x:(A => B)
render_bussproofs(cq_c(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $ CQ_{c}$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% CQ_m : Regle de conversion minimale (?x:A => B) => ?x:(A => B)
render_bussproofs(cq_m(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $ CQ_{m}$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.


% =========================================================================
% REGLES D'EGALITE - VERSION CORRIGEE
% =========================================================================

% Reflexivite : Seq = [t = t] (pas de tuple)
render_bussproofs(eq_refl(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize $ Refl$}'), nl,
    write('\\UnaryInfC{$'),
    write(' \\vdash '),
    ( Seq = [Goal] -> 
        rewrite(Goal, VarCounter, FinalCounter, GoalLatex),
        write(GoalLatex)
    ;
        render_sequent(Seq, VarCounter, FinalCounter)
    ),
    write('$}'), nl.

% Symetrie
render_bussproofs(eq_sym(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize $ Sym$}'),  nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% Transitivite simple
render_bussproofs(eq_trans(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize $ Trans$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% Transitivite chainee
render_bussproofs(eq_trans_chain(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize $ Trans^*$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% Congruence
render_bussproofs(eq_cong(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize $ Cong$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% Substitution dans egalite
render_bussproofs(eq_subst_eq(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize $ Subst_{eq}$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% Substitution (Leibniz)
render_bussproofs(eq_subst(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize $ Leibniz$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% Substitution pour equivalence logique
render_bussproofs(equiv_subst(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize $ \\equiv$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.


% Filter 
render_sequent(G > D, VarCounter, FinalCounter) :-
    % TOUJOURS utiliser G du sequent, PAS premise_list !
    filter_top_from_gamma(G, FilteredG),
    
    ( FilteredG = [] ->
        % Theoreme : pas de premisses a afficher
        write(' \\vdash '),
        TempCounter = VarCounter
    ;
        % Sequent avec premisses
        render_formula_list(FilteredG, VarCounter, TempCounter),
        write(' \\vdash ')
    ),
    ( D = [] ->
        write('\\bot'),
        FinalCounter = TempCounter
    ;
        render_formula_list(D, TempCounter, FinalCounter)
    ).


% filter_top_from_gamma/2: Enleve ? (top) de la liste de premisses
filter_top_from_gamma([], []).
filter_top_from_gamma([H|T], Filtered) :-
    ( is_top_formula(H) ->
        filter_top_from_gamma(T, Filtered)
    ;
        filter_top_from_gamma(T, RestFiltered),
        Filtered = [H|RestFiltered]
    ).

% is_top_formula/1: Detecte si une formule est ? (top)
% ? est represente comme (# => #) ou parfois ~ #
is_top_formula((# => #)) :- !.
is_top_formula(((# => #) => #) => #) :- !.  % Double negation de ?
is_top_formula(_) :- fail.

% =========================================================================
% RENDU DES LISTES DE FORMULES
% =========================================================================

% Liste vide
render_formula_list([], VarCounter, VarCounter) :- !.

% Formule unique
render_formula_list([F], VarCounter, FinalCounter) :-
    !,
    rewrite(F, VarCounter, FinalCounter, F_latex),
    write_formula_with_parens(F_latex).

% Liste de formules avec virgules
render_formula_list([F|Rest], VarCounter, FinalCounter) :-
    rewrite(F, VarCounter, TempCounter, F_latex),
    write(F_latex),
    write(', '),
    render_formula_list(Rest, TempCounter, FinalCounter).

% =========================================================================
% INTEGRATION AVEC LE SYSTEME PRINCIPAL
% =========================================================================

% Interface compatible avec decide/1
render_g4_bussproofs_from_decide(Proof) :-
    render_g4_proof(Proof).

% Interface compatible avec prove_formula_clean/3
render_g4_bussproofs_from_clean(Proof) :-
    render_g4_proof(Proof).

% =========================================================================
% COMMENTAIRES ET DOCUMENTATION
% =========================================================================

% Ce printer G4 est specialement optimise pour :
% 
% 1. LES REGLES G4 AUTHENTIQUES :
%    - L0-> (modus ponens signature de G4)
%    - L?->, L?-> (transformations curryifiees)
%    - L->-> (regle G4 speciale)
%    - Ordre exact du multiprover.pl
%
% 2. COMPATIBILITE MULTIFORMATS :
%    - Utilise le systeme rewrite/4 de latex_utilities.pl
%    - Compatible avec les quantificateurs FOL
%    - Gere les antisequents pour les echecs
%
% 3. RENDU LATEX PROFESSIONNEL :
%    - bussproofs.sty standard
%    - Labels compacts et clairs
%    - Gestion automatique des compteurs de variables
%
% USAGE :
% ?- decide(Formula).  % Utilise automatiquement ce printer
% ?- render_g4_proof(Proof).  % Rendu direct d'une preuve

% =========================================================================
% FIN DU G4 PRINTER
% =========================================================================
% =========================================================================
% GESTION DES TERMES CYCLIQUES
% =========================================================================
make_acyclic_term(Term, Safe) :-
    catch(
        make_acyclic_term(Term, [], _MapOut, Safe),
        _,
        Safe = cyc(Term)
    ).

make_acyclic_term(Term, MapIn, MapOut, Safe) :-
    ( var(Term) ->
        Safe = Term, MapOut = MapIn
    ; atomic(Term) ->
        Safe = Term, MapOut = MapIn
    ; find_pair(Term, MapIn, Value) ->
        Safe = Value, MapOut = MapIn
    ;
        gensym(cyc, Patom),
        Placeholder = cyc(Patom),
        MapMid = [pair(Term, Placeholder)|MapIn],
        Term =.. [F|Args],
        make_acyclic_args(Args, MapMid, MapAfterArgs, SafeArgs),
        SafeTermBuilt =.. [F|SafeArgs],
        replace_pair(Term, Placeholder, SafeTermBuilt, MapAfterArgs, MapOut),
        Safe = SafeTermBuilt
    ).

make_acyclic_args([], Map, Map, []).
make_acyclic_args([A|As], MapIn, MapOut, [SA|SAs]) :-
    make_acyclic_term(A, MapIn, MapMid, SA),
    make_acyclic_args(As, MapMid, MapOut, SAs).

find_pair(Term, [pair(Orig,Val)|_], Val) :- Orig == Term, !.
find_pair(Term, [_|Rest], Val) :- find_pair(Term, Rest, Val).

replace_pair(Term, OldVal, NewVal, [pair(Orig,OldVal)|Rest], [pair(Orig,NewVal)|Rest]) :- 
    Orig == Term, !.
replace_pair(Term, OldVal, NewVal, [H|T], [H|T2]) :- 
    replace_pair(Term, OldVal, NewVal, T, T2).
replace_pair(_, _, _, [], []).


% =========================================================================
% HELPERS COMBINATORS
% =========================================================================
% Helper : Enlever TOUTES les annotations (pas juste les quantificateurs)
strip_annotations_deep(@(Term, _), Stripped) :- !, strip_annotations_deep(Term, Stripped).
strip_annotations_deep(![_-X]:Body, ![X]:StrippedBody) :- !, strip_annotations_deep(Body, StrippedBody).
strip_annotations_deep(?[_-X]:Body, ?[X]:StrippedBody) :- !, strip_annotations_deep(Body, StrippedBody).
strip_annotations_deep(A & B, SA & SB) :- !, strip_annotations_deep(A, SA), strip_annotations_deep(B, SB).
strip_annotations_deep(A | B, SA | SB) :- !, strip_annotations_deep(A, SA), strip_annotations_deep(B, SB).
strip_annotations_deep(A => B, SA => SB) :- !, strip_annotations_deep(A, SA), strip_annotations_deep(B, SB).
strip_annotations_deep(A <=> B, SA <=> SB) :- !, strip_annotations_deep(A, SA), strip_annotations_deep(B, SB).
strip_annotations_deep(Term, Term).
% =========================================================================
% HELPERS COMBINATORS
% =========================================================================
derive_and_continue(Scope, Formula, RuleTemplate, Refs, RuleTerm, SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    derive_formula(Scope, Formula, RuleTemplate, Refs, RuleTerm, CurLine, DerivLine, _, VarIn, V1),
    fitch_g4_proof(SubProof, [DerivLine:Formula|Context], Scope, DerivLine, NextLine, ResLine, V1, VarOut).

derive_formula(Scope, Formula, RuleTemplate, Refs, RuleTerm, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    NextLine is CurLine + 1,
    assert_safe_fitch_line(NextLine, Formula, RuleTerm, Scope),
    format(atom(Just), RuleTemplate, Refs),
    render_have(Scope, Formula, Just, CurLine, NextLine, VarIn, VarOut),
    ResLine = NextLine.

assume_in_scope(Assumption, _Goal, SubProof, Context, ParentScope, StartLine, EndLine, GoalLine, VarIn, VarOut) :-
    AssLine is StartLine + 1,
    assert_safe_fitch_line(AssLine, Assumption, assumption, ParentScope),
    render_hypo(ParentScope, Assumption, 'AS', StartLine, AssLine, VarIn, V1),
    NewScope is ParentScope + 1,
    fitch_g4_proof(SubProof, [AssLine:Assumption|Context], NewScope, AssLine, EndLine, GoalLine, V1, VarOut).
% =========================================================================
% EXTRACTION & HELPERS
% =========================================================================
extract_new_formula(CurrentPremisses, SubProof, NewFormula) :-
    SubProof =.. [_Rule|[(SubPremisses > _SubGoal)|_]],
    member(NewFormula, SubPremisses),
    \+ member(NewFormula, CurrentPremisses),
    !.
extract_new_formula(_CurrentPremisses, SubProof, NewFormula) :-
    SubProof =.. [_Rule|[(SubPremisses > _SubGoal)|_]],
    member(NewFormula, SubPremisses),
    \+ is_quantified(NewFormula),
    !.
extract_new_formula(CurrentPremisses, SubProof, _) :-
    format('% ERROR extract_new_formula: No suitable formula found~n', []),
    format('%   CurrentPremisses: ~w~n', [CurrentPremisses]),
    SubProof =.. [Rule|[(SubPremisses > _)|_]],
    format('%   SubProof rule: ~w~n', [Rule]),
    format('%   SubPremisses: ~w~n', [SubPremisses]),
    fail.
% =========================================================================
% FIND_CONTEXT_LINE : Matcher formules dans le contexte
% =========================================================================
% =========================================================================
% PRIORITE ABSOLUE : PREMISSES (lignes 1-N ou N = nombre de premisses)
% =========================================================================

find_context_line(Formula, Context, LineNumber) :-
    premise_list(PremList),
    length(PremList, NumPremises),
    % Chercher UNIQUEMENT dans les N premieres lignes
    member(LineNumber:ContextFormula, Context),
    LineNumber =< NumPremises,
    % Matcher avec les differentes variantes possibles
    ( ContextFormula = Formula
    ; strip_annotations_match(Formula, ContextFormula)
    ; formulas_equivalent(Formula, ContextFormula)
    ),
    !.  % Couper des qu'on trouve dans les premisses

% =========================================================================
% PRIORITE -1 : NEGATION DE QUANTIFICATEUR (forme originale ~)
% =========================================================================

% Cherche (![x-x]:Body) => # mais contexte a ~![x]:Body (forme originale)
find_context_line((![_Z-_X]:Body) => #, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        % Forme originale avec ~
        ContextFormula = (~ ![_]:Body)
    ;
        % Forme transformee
        ContextFormula = ((![_]:Body) => #)
    ;
        % Forme transformee avec annotation
        ContextFormula = ((![_-_]:Body) => #)
    ),
    !.

% Meme chose pour l'existentiel
find_context_line((?[_Z-_X]:Body) => #, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        ContextFormula = (~ ?[_]:Body)
    ;
        ContextFormula = ((?[_]:Body) => #)
    ;
        ContextFormula = ((?[_-_]:Body) => #)
    ),
    !.
% =========================================================================
% PRIORITE 0 : QUANTIFICATEURS - MATCHER STRUCTURE INTERNE COMPLEXE
% =========================================================================
% Universel : matcher structure interne independamment de la transformation
find_context_line(![Z-_]:SearchBody, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        % Cas 1: Contexte sans annotation
        ContextFormula = (![Z]:ContextBody),
        formulas_equivalent(SearchBody, ContextBody)
    ;
        % Cas 2: Contexte avec annotation
        ContextFormula = (![Z-_]:ContextBody),
        formulas_equivalent(SearchBody, ContextBody)
    ),
    !.

% Existentiel : matcher structure interne
find_context_line(?[Z-_]:SearchBody, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        ContextFormula = (?[Z]:ContextBody),
        formulas_equivalent(SearchBody, ContextBody)
    ;
        ContextFormula = (?[Z-_]:ContextBody),
        formulas_equivalent(SearchBody, ContextBody)
    ),
    !.

% -------------------------------------------------------------------------
% PRIORITE 1 : NEGATIONS (notation originale ~ vs transformee => #)
% -------------------------------------------------------------------------

% Cas 1: Cherche ?[x]:A => # mais contexte a ~ ?[x]:A
find_context_line((?[Z-_]:A) => #, Context, LineNumber) :-
    member(LineNumber:(~ ?[Z]:A), Context), !.

% Cas 2: Cherche ![x]:(A => #) mais contexte a ![x]: ~A
find_context_line(![Z-_]:(A => #), Context, LineNumber) :-
    member(LineNumber:(![Z]: ~A), Context), !.

% Cas 3: Cherche A => # mais contexte a ~A (formule simple)
find_context_line(A => #, Context, LineNumber) :-
    A \= (?[_]:_),
    A \= (![_]:_),
    member(LineNumber:(~A), Context), !.

% -------------------------------------------------------------------------
% PRIORITE 2 : QUANTIFICATEURS (avec/sans annotations de variables)
% -------------------------------------------------------------------------

% Universel : cherche ![x-x]:Body mais contexte a ![x]:Body
find_context_line(![Z-_]:Body, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        ContextFormula = (![Z]:Body)      % Sans annotation
    ;
        ContextFormula = (![Z-_]:Body)    % Avec annotation differente
    ),
    !.

% Existentiel : cherche ?[x-x]:Body mais contexte a ?[x]:Body
find_context_line(?[Z-_]:Body, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        ContextFormula = (?[Z]:Body)      % Sans annotation
    ;
        ContextFormula = (?[Z-_]:Body)    % Avec annotation differente
    ),
    !.

% -------------------------------------------------------------------------
% PRIORITE 3 : BICONDITIONNELLES (decomposees)
% -------------------------------------------------------------------------

find_context_line((A => B) & (B => A), Context, LineNumber) :-
    member(LineNumber:(A <=> B), Context), !.

find_context_line((B => A) & (A => B), Context, LineNumber) :-
    member(LineNumber:(A <=> B), Context), !.

% -------------------------------------------------------------------------
% PRIORITE 4 : MATCH EXACT
% -------------------------------------------------------------------------

find_context_line(Formula, Context, LineNumber) :-
    member(LineNumber:Formula, Context), !.

% -------------------------------------------------------------------------
% PRIORITE 5 : UNIFICATION
% -------------------------------------------------------------------------

find_context_line(Formula, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    unify_with_occurs_check(Formula, ContextFormula), !.

% -------------------------------------------------------------------------
% PRIORITE 6 : STRUCTURE MATCHING
% -------------------------------------------------------------------------

find_context_line(Formula, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    match_formula_structure(Formula, ContextFormula), !.

% -------------------------------------------------------------------------
% FALLBACK : WARNING si aucune correspondance
% -------------------------------------------------------------------------

find_context_line(Formula, _Context, 0) :-
    format('% WARNING: Formula ~w not found in context~n', [Formula]).

% =========================================================================
% HELPER : Equivalence de formules (comparaison structurelle pure)
% =========================================================================

% Helper : matcher en enlevant les annotations
strip_annotations_match(![_-X]:Body, ![X]:Body) :- !.
strip_annotations_match(![X]:Body, ![_-X]:Body) :- !.
strip_annotations_match(?[_-X]:Body, ?[X]:Body) :- !.
strip_annotations_match(?[X]:Body, ?[_-X]:Body) :- !.
strip_annotations_match(A, B) :- A = B.


% Biconditionnelle : matcher structure sans regarder l'ordre
formulas_equivalent((A1 => B1) & (B2 => A2), C <=> D) :- 
    !,
    (
        (formulas_equivalent(A1, C), formulas_equivalent(A2, C),
         formulas_equivalent(B1, D), formulas_equivalent(B2, D))
    ;
        (formulas_equivalent(A1, D), formulas_equivalent(A2, D),
         formulas_equivalent(B1, C), formulas_equivalent(B2, C))
    ).

formulas_equivalent(A <=> B, (C => D) & (D2 => C2)) :- 
    !,
    (
        (formulas_equivalent(A, C), formulas_equivalent(A, C2),
         formulas_equivalent(B, D), formulas_equivalent(B, D2))
    ;
        (formulas_equivalent(A, D), formulas_equivalent(A, D2),
         formulas_equivalent(B, C), formulas_equivalent(B, C2))
    ).

formulas_equivalent((A <=> B), (C <=> D)) :- 
    !,
    (
        (formulas_equivalent(A, C), formulas_equivalent(B, D))
    ;
        (formulas_equivalent(A, D), formulas_equivalent(B, C))
    ).

% Negation transformee
formulas_equivalent(A => #, ~ B) :- !, formulas_equivalent(A, B).
formulas_equivalent(~ A, B => #) :- !, formulas_equivalent(A, B).

% Quantificateurs : comparer corps uniquement (ignorer variable)
formulas_equivalent(![_]:Body1, ![_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(![_-_]:Body1, ![_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(![_]:Body1, ![_-_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(![_-_]:Body1, ![_-_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).

formulas_equivalent(?[_]:Body1, ?[_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(?[_-_]:Body1, ?[_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(?[_]:Body1, ?[_-_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(?[_-_]:Body1, ?[_-_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).

% Connecteurs binaires
formulas_equivalent(A & B, C & D) :- 
    !, formulas_equivalent(A, C), formulas_equivalent(B, D).
formulas_equivalent(A | B, C | D) :- 
    !, formulas_equivalent(A, C), formulas_equivalent(B, D).
formulas_equivalent(A => B, C => D) :- 
    !, formulas_equivalent(A, C), formulas_equivalent(B, D).

% Faux
formulas_equivalent(#, #) :- !.

% Predicats/Termes : comparer structure (ignorer variables)
formulas_equivalent(Term1, Term2) :-
    compound(Term1),
    compound(Term2),
    !,
    Term1 =.. [Functor|_Args1],
    Term2 =.. [Functor|_Args2],
    % Meme foncteur suffit (on ignore les arguments qui sont des variables)
    !.

% Identite stricte
formulas_equivalent(A, B) :- A == B, !.

% Fallback : termes atomiques avec meme nom
formulas_equivalent(A, B) :- 
    atomic(A), atomic(B),
    !.

% Helper : matcher deux formules par structure (module renommage de variables)
% Negations
match_formula_structure(A => #, B => #) :- 
    !, match_formula_structure(A, B).
match_formula_structure(~A, B => #) :- 
    !, match_formula_structure(A, B).
match_formula_structure(A => #, ~ B) :- 
    !, match_formula_structure(A, B).
match_formula_structure(~ A, ~ B) :- 
    !, match_formula_structure(A, B).

% Quantificateurs
match_formula_structure(![_-_]:Body1, ![_-_]:Body2) :-
    !, match_formula_structure(Body1, Body2).
match_formula_structure(?[_-_]:Body1, ?[_-_]:Body2) :-
    !, match_formula_structure(Body1, Body2).

% Connecteurs binaires
match_formula_structure(A & B, C & D) :-
    !, match_formula_structure(A, C), match_formula_structure(B, D).
match_formula_structure(A | B, C | D) :-
    !, match_formula_structure(A, C), match_formula_structure(B, D).
match_formula_structure(A => B, C => D) :-
    !, match_formula_structure(A, C), match_formula_structure(B, D).
match_formula_structure(A <=> B, C <=> D) :-
    !, match_formula_structure(A, C), match_formula_structure(B, D).

% Faux
match_formula_structure(#, #) :- !.

% Egalite stricte
match_formula_structure(A, B) :-
    A == B, !.

% Subsomption
match_formula_structure(A, B) :-
    subsumes_term(A, B) ; subsumes_term(B, A).


find_disj_context(L, R, Context, Line) :-
    ( member(Line:(CL | CR), Context), subsumes_term((L | R), (CL | CR)) -> true
    ; member(Line:(CL | CR), Context), \+ \+ ((L = CL, R = CR))
    ).

extract_witness(SubProof, Witness) :-
    SubProof =.. [Rule|Args],
    Args = [(Prem > _)|_],
    ( member(Witness, Prem), contains_skolem(Witness), ( Rule = rall ; Rule = lall ; \+ is_quantified(Witness) ) ), !.
extract_witness(SubProof, Witness) :-
    SubProof =.. [_, (_ > _), SubSP|_],
    extract_witness(SubSP, Witness).

is_quantified(![_-_]:_) :- !.
is_quantified(?[_-_]:_) :- !.

contains_skolem(Formula) :-
    Formula =.. [_|Args],
    member(Arg, Args),
    (Arg = f_sk(_,_) ; compound(Arg), contains_skolem(Arg)).

is_direct_conjunct(G, (A & B)) :- (G = A ; G = B), !.
is_direct_conjunct(G, (A & R)) :- (G = A ; is_direct_conjunct(G, R)).

extract_conjuncts((A & B), CLine, Scope, CurLine, [L1:A, L2:B], L2, VarIn, VarOut) :-
    L1 is CurLine + 1,
    L2 is CurLine + 2,
    assert_safe_fitch_line(L1, A, land(CLine), Scope),
    assert_safe_fitch_line(L2, B, land(CLine), Scope),
    format(atom(Just1), '$ \\land E $ ~w', [CLine]),
    format(atom(Just2), '$ \\land E $ ~w', [CLine]),
    render_have(Scope, A, Just1, CurLine, L1, VarIn, V1),
    render_have(Scope, B, Just2, L1, L2, V1, VarOut).
% =========================================================================
% LOGIQUE DE DERIVATION IMMEDIATE
% =========================================================================
derive_immediate(Scope, Formula, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, Formula, RuleTerm, Scope),
    format(atom(Just), JustFormat, JustArgs),
    render_have(Scope, Formula, Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

try_derive_immediately(Goal, Context, _Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    member(ResLine:Goal, Context),
    !,
    NextLine = CurLine,
    VarOut = VarIn.

try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    member(MajLine:(Ant => Goal), Context),
    member(MinLine:Ant, Context),
    !,
    RuleTerm = l0cond(MajLine, MinLine),
    JustFormat = '$ \\to E $ ~w,~w',
    JustArgs = [MajLine, MinLine],
    derive_immediate(Scope, Goal, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut).

try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    member(ConjLine:(A & B), Context),
    (Goal = A ; Goal = B),
    !,
    RuleTerm = land(ConjLine),
    JustFormat = '$ \\land E $ ~w',
    JustArgs = [ConjLine],
    derive_immediate(Scope, Goal, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut).

try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    member(FLine: #, Context),
    !,
    RuleTerm = lbot(FLine),
    JustFormat = '$ \\bot E $ ~w',
    JustArgs = [FLine],
    derive_immediate(Scope, Goal, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut).

try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    Goal = (L | R),
    ( member(SLine:L, Context) -> true ; member(SLine:R, Context) ),
    !,
    RuleTerm = ror(SLine),
    JustFormat = '$ \\lor I $ ~w',
    JustArgs = [SLine],
    derive_immediate(Scope, Goal, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut).

try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    Goal = (L & R),
    member(LLine:L, Context),
    member(RLine:R, Context),
    !,
    RuleTerm = rand(LLine, RLine),
    JustFormat = '$ \\land I $ ~w,~w',
    JustArgs = [LLine, RLine],
    derive_immediate(Scope, Goal, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut).

% =========================================================================
% CONSTRUCTION DE LA MAP DES HYPOTHESES PARTAGEES
% =========================================================================

build_hypothesis_map([], Map, Map).
build_hypothesis_map([N-Formula-assumption-Scope|Rest], AccMap, FinalMap) :-
    !,
    ( member(M-Formula-assumption-Scope, Rest), M > N ->
        build_hypothesis_map(Rest, [M-N|AccMap], FinalMap)
    ;
        build_hypothesis_map(Rest, AccMap, FinalMap)
    ).
build_hypothesis_map([_|Rest], AccMap, FinalMap) :-
    build_hypothesis_map(Rest, AccMap, FinalMap).

% =========================================================================
% End of common ND PRINTING
% =========================================================================

% =========================================================================
% NATURAL DEDUCTION PRINTER IN FLAG STYLE  
% =========================================================================
:- dynamic fitch_line/4.
:- dynamic abbreviated_line/1.
% =========================================================================
% FROM G4 Sequent Calculus To Natural Deduction in Fitch Style 
% =========================================================================
g4_to_fitch_sequent(Proof, OriginalSequent) :-
    !,
    retractall(fitch_line(_, _, _, _)),
    retractall(abbreviated_line(_)),
    
    OriginalSequent = (_G > [Conclusion]),
    
    ( premise_list(PremList), PremList \= [] ->
        render_premise_list(PremList, 0, 1, NextLine, InitialContext),
        LastPremLine is NextLine - 1  % ? CORRECTION : derniere ligne de premisse
    ;
        _NextLine = 1,
        LastPremLine = 0,             % ? CORRECTION : pas de premisses
        InitialContext = []
    ),
    
    % ? CORRECTION : Scope=1 (indentation), CurLine=LastPremLine (numerotation)
    fitch_g4_proof(Proof, InitialContext, 1, LastPremLine, LastLine, ResLine, 0, _),
    
    % DETECTER : Est-ce qu'une regle a ete appliquee ?
    ( LastLine = LastPremLine ->
        % Aucune ligne ajoutee -> axiome pur -> afficher reiteration
        write('\\fa '),
        rewrite(Conclusion, 0, _, LatexConclusion),
        write(LatexConclusion),
        format(' &  R ~w\\\\', [ResLine]), nl
    ;
        % Une regle a deja affiche la conclusion -> ne rien faire
        true
    ).

% g4_to_fitch_theorem/1 : Pour theoremes (comportement original)
g4_to_fitch_theorem(Proof) :-
    retractall(fitch_line(_, _, _, _)),
    retractall(abbreviated_line(_)),
    fitch_g4_proof(Proof, [], 1, 0, _, _, 0, _).
% =========================================================================
% AFFICHAGE DES PREMISSES
% =========================================================================
% render_premise_list/5: Affiche une liste de premisses en Fitch
render_premise_list([], _, Line, Line, []) :- !.

render_premise_list([LastPremiss], Scope, CurLine, NextLine, [CurLine:LastPremiss]) :-
    !,
    render_fitch_indent(Scope),
    write(' \\fj '),
    rewrite(LastPremiss, 0, _, LatexFormula),
    write(LatexFormula),
    write(' &  PR\\\\'), nl,
    assert_safe_fitch_line(CurLine, LastPremiss, premise, Scope),
    NextLine is CurLine + 1.
    
render_premise_list([Premiss|Rest], Scope, CurLine, NextLine, [CurLine:Premiss|RestContext]) :-
    render_fitch_indent(Scope),
    write(' \\fa '),
    rewrite(Premiss, 0, _, LatexFormula),
    write(LatexFormula),
    write(' &  PR\\\\'), nl,
    assert_safe_fitch_line(CurLine, Premiss, premise, Scope),
    NextCurLine is CurLine + 1,
    render_premise_list(Rest, Scope, NextCurLine, NextLine, RestContext).
% =========================================================================
% ASSERTION SECURISEE
% =========================================================================
assert_safe_fitch_line(N, Formula, Just, Scope) :-
    catch(
        (
            ( acyclic_term(Formula) ->
                Safe = Formula
            ;
                make_acyclic_term(Formula, Safe)
            ),
            assertz(fitch_line(N, Safe, Just, Scope))
        ),
        Error,
        (
            format('% Warning: Could not assert line ~w: ~w~n', [N, Error]),
            assertz(fitch_line(N, error_term(Formula), Just, Scope))
        )
    ).
% =========================================================================
% GESTION DES TERMES CYCLIQUES
% =========================================================================
/*
make_acyclic_term(Term, Safe) :-
    catch(
        make_acyclic_term(Term, [], _MapOut, Safe),
        _,
        Safe = cyc(Term)
    ).

make_acyclic_term(Term, MapIn, MapOut, Safe) :-
    ( var(Term) ->
        Safe = Term, MapOut = MapIn
    ; atomic(Term) ->
        Safe = Term, MapOut = MapIn
    ; find_pair(Term, MapIn, Value) ->
        Safe = Value, MapOut = MapIn
    ;
        gensym(cyc, Patom),
        Placeholder = cyc(Patom),
        MapMid = [pair(Term, Placeholder)|MapIn],
        Term =.. [F|Args],
        make_acyclic_args(Args, MapMid, MapAfterArgs, SafeArgs),
        SafeTermBuilt =.. [F|SafeArgs],
        replace_pair(Term, Placeholder, SafeTermBuilt, MapAfterArgs, MapOut),
        Safe = SafeTermBuilt
    ).

make_acyclic_args([], Map, Map, []).
make_acyclic_args([A|As], MapIn, MapOut, [SA|SAs]) :-
    make_acyclic_term(A, MapIn, MapMid, SA),
    make_acyclic_args(As, MapMid, MapOut, SAs).

find_pair(Term, [pair(Orig,Val)|_], Val) :- Orig == Term, !.
find_pair(Term, [_|Rest], Val) :- find_pair(Term, Rest, Val).

replace_pair(Term, OldVal, NewVal, [pair(Orig,OldVal)|Rest], [pair(Orig,NewVal)|Rest]) :- 
    Orig == Term, !.
replace_pair(Term, OldVal, NewVal, [H|T], [H|T2]) :- 
    replace_pair(Term, OldVal, NewVal, T, T2).
replace_pair(_, _, _, [], []).
*/
% =========================================================================
% GESTION DES SUBSTITUTIONS @
% =========================================================================

fitch_g4_proof(@(ProofTerm, _), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    fitch_g4_proof(ProofTerm, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut).

% =========================================================================
% AXIOME
% =========================================================================

fitch_g4_proof(ax((Premisses > [Goal]), _Tag), Context, _Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    member(Goal, Premisses),
    find_context_line(Goal, Context, GoalLine),
    NextLine = CurLine,
    ResLine = GoalLine,
    VarOut = VarIn.

fitch_g4_proof(ax((Premisses > [Goal])), Context, _Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    member(Goal, Premisses),
    find_context_line(Goal, Context, GoalLine),
    NextLine = CurLine,
    ResLine = GoalLine,
    VarOut = VarIn.

% =========================================================================
% PROPOSITIONAL RULES 
% =========================================================================
% L0-> 
fitch_g4_proof(l0cond((Premisss > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    select((Ant => Cons), Premisss, Remaining),
    member(Ant, Remaining),
    find_context_line((Ant => Cons), Context, MajLine),
    find_context_line(Ant, Context, MinLine),
    DerLine is CurLine + 1,
    format(atom(Just), '$ \\to E $ ~w,~w', [MajLine, MinLine]),
    render_have(Scope, Cons, Just, CurLine, DerLine, VarIn, V1),
    assert_safe_fitch_line(DerLine, Cons, l0cond(MajLine, MinLine), Scope),
    fitch_g4_proof(SubProof, [DerLine:Cons|Context], Scope, DerLine, NextLine, ResLine, V1, VarOut).

% L?-> 
fitch_g4_proof(landto((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    extract_new_formula(Premisses, SubProof, NewFormula),
    select(((A & B) => C), Premisses, _),
    once(member(ImpLine:((A & B) => C), Context)),
    derive_and_continue(Scope, NewFormula, 'L$ \\land \\to $ ~w', [ImpLine],
                       landto(ImpLine), SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut).

% L?-> : Disjunction to implications
fitch_g4_proof(lorto((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    SubProof =.. [_Rule|[(SubPremisses > _SubGoal)|_]],
    findall(F, (member(F, SubPremisses), \+ member(F, Premisses)), NewFormulas),
    select(((A | B) => C), Premisses, _),
    find_context_line(((A | B) => C), Context, ImpLine),
    ( NewFormulas = [F1, F2] ->
        Line1 is CurLine + 1,
        Line2 is CurLine + 2,
        assert_safe_fitch_line(Line1, F1, lorto(ImpLine), Scope),
        assert_safe_fitch_line(Line2, F2, lorto(ImpLine), Scope),
        format(atom(Just), 'L$ \\lor \\to $ ~w', [ImpLine]),
        render_have(Scope, F1, Just, CurLine, Line1, VarIn, V1),
        render_have(Scope, F2, Just, Line1, Line2, V1, V2),
        fitch_g4_proof(SubProof, [Line2:F2, Line1:F1|Context], Scope, Line2, NextLine, ResLine, V2, VarOut)
    ; NewFormulas = [F1] ->
        derive_and_continue(Scope, F1, 'L$ \\lor \\to $ ~w', [ImpLine],
                           lorto(ImpLine), SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut)
    ;
        fitch_g4_proof(SubProof, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut)
    ).

% L? : Conjunction elimination
fitch_g4_proof(land((Premisses > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    select((A & B), Premisses, _),
   % member(ConjLine:(A & B), Context), ligne corrigee par la suivante
    find_context_line((A & B), Context, ConjLine),
    ( is_direct_conjunct(Goal, (A & B)) ->
        derive_formula(Scope, Goal, '$ \\land E $ ~w', [ConjLine], land(ConjLine),
                      CurLine, NextLine, ResLine, VarIn, VarOut)
    ;
        extract_conjuncts((A & B), ConjLine, Scope, CurLine, ExtCtx, LastLine, VarIn, V1),
        append(ExtCtx, Context, NewCtx),
        fitch_g4_proof(SubProof, NewCtx, Scope, LastLine, NextLine, ResLine, V1, VarOut)
    ).

% L? : Explosion
fitch_g4_proof(lbot((Premisss > [Goal]), _), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    member(#, Premisss),
    member(FalseLine: #, Context),
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, Goal, lbot(FalseLine), Scope),
    format(atom(Just), '$ \\bot E $ ~w', [FalseLine]),
    render_have(Scope, Goal, Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% R? : Disjunction introduction
fitch_g4_proof(ror((_ > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    ( Goal = (_ | _), try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) ->
        true
    ; fitch_g4_proof(SubProof, Context, Scope, CurLine, SubEnd, DisjunctLine, VarIn, V1),
      OrLine is SubEnd + 1,
      assert_safe_fitch_line(OrLine, Goal, ror(DisjunctLine), Scope),
      format(atom(Just), '$ \\lor I $ ~w', [DisjunctLine]),
      render_have(Scope, Goal, Just, SubEnd, OrLine, V1, VarOut),
      NextLine = OrLine,
      ResLine = OrLine
    ).

% =========================================================================
% REGLES AVEC HYPOTHESES (ASSUME-DISCHARGE)
% =========================================================================

% R-> : Implication introduction
fitch_g4_proof(rcond((_ > [A => B]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    HypLine is CurLine + 1,
    assert_safe_fitch_line(HypLine, A, assumption, Scope),
    render_hypo(Scope, A, 'AS', CurLine, HypLine, VarIn, V1),
    NewScope is Scope + 1,
    fitch_g4_proof(SubProof, [HypLine:A|Context], NewScope, HypLine, SubEnd, GoalLine, V1, V2),
    ImplLine is SubEnd + 1,
    assert_safe_fitch_line(ImplLine, (A => B), rcond(HypLine, GoalLine), Scope),
    format(atom(Just), '$ \\to I $ ~w-~w', [HypLine, GoalLine]),
    render_have(Scope, (A => B), Just, SubEnd, ImplLine, V2, VarOut),
    NextLine = ImplLine,
    ResLine = ImplLine.

% TNE : Triple negation elimination
fitch_g4_proof(tne((_ > [(A => B)]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    HypLine is CurLine + 1,
    assert_safe_fitch_line(HypLine, A, assumption, Scope),
    render_hypo(Scope, A, 'AS', CurLine, HypLine, VarIn, V1),
    NewScope is Scope + 1,
    fitch_g4_proof(SubProof, [HypLine:A|Context], NewScope, HypLine, SubEnd, GoalLine, V1, V2),
    ImplLine is SubEnd + 1,
    assert_safe_fitch_line(ImplLine, (A => B), rcond(HypLine, GoalLine), Scope),
    format(atom(Just), '$ \\to I $ ~w-~w', [HypLine, GoalLine]),
    render_have(Scope, (A => B), Just, SubEnd, ImplLine, V2, VarOut),
    NextLine = ImplLine,
    ResLine = ImplLine.

% IP : Indirect proof / Classical
fitch_g4_proof(ip((_ > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    ( Goal = (A => #) ->
        Assumption = ((A => #) => #),
        Rule = 'DNE_m'
    ;
        Assumption = (Goal => #),
        Rule = 'IP'
    ),
    HypLine is CurLine + 1,
    assert_safe_fitch_line(HypLine, Assumption, assumption, Scope),
    render_hypo(Scope, Assumption, 'AS', CurLine, HypLine, VarIn, V1),
    NewScope is Scope + 1,
    fitch_g4_proof(SubProof, [HypLine:Assumption|Context], NewScope, HypLine, SubEnd, BotLine, V1, V2),
    IPLine is SubEnd + 1,
    assert_safe_fitch_line(IPLine, Goal, ip(HypLine, BotLine), Scope),
    format(atom(Just), '~w ~w-~w', [Rule, HypLine, BotLine]),
    render_have(Scope, Goal, Just, SubEnd, IPLine, V2, VarOut),
    NextLine = IPLine,
    ResLine = IPLine.

% L? : Disjunction elimination
fitch_g4_proof(lor((Premisss > [Goal]), SP1, SP2), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    ( try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) ->
       true
    ; 
      select((A | B), Premisss, _),
      % First try to find the disjunction in the context, otherwise in premises
      ( find_disj_context(A, B, Context, DisjLine) ->
          true
      ;
          % Disjunction is a premise, find its line
          find_context_line((A | B), Context, DisjLine)
      ),
      AssLineA is CurLine + 1,
      assert_safe_fitch_line(AssLineA, A, assumption, Scope),
      render_hypo(Scope, A, 'AS', CurLine, AssLineA, VarIn, V1),
      NewScope is Scope + 1,
      fitch_g4_proof(SP1, [AssLineA:A|Context], NewScope, AssLineA, EndA, GoalA, V1, V2),
      AssLineB is EndA + 1,
      assert_safe_fitch_line(AssLineB, B, assumption, Scope),
      render_hypo(Scope, B, 'AS', EndA, AssLineB, V2, V3),
      fitch_g4_proof(SP2, [AssLineB:B|Context], NewScope, AssLineB, EndB, GoalB, V3, V4),
      ElimLine is EndB + 1,
      assert_safe_fitch_line(ElimLine, Goal, lor(DisjLine, AssLineA, AssLineB, GoalA, GoalB), Scope),
      format(atom(Just), '$ \\lor E $ ~w,~w-~w,~w-~w', [DisjLine, AssLineA, GoalA, AssLineB, GoalB]),
      render_have(Scope, Goal, Just, EndB, ElimLine, V4, VarOut),
      NextLine = ElimLine,
      ResLine = ElimLine
    ).

% =========================================================================
% REGLES BINAIRES
% =========================================================================

% R? : Conjunction introduction
fitch_g4_proof(rand((_ > [Goal]), SP1, SP2), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    Goal = (L & _R),
    ( try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) -> true
    ; fitch_g4_proof(SP1, Context, Scope, CurLine, End1, LeftLine, VarIn, V1),
      fitch_g4_proof(SP2, [LeftLine:L|Context], Scope, End1, End2, RightLine, V1, V2),
      derive_formula(Scope, Goal, '$ \\land I $ ~w,~w', [LeftLine, RightLine], rand(LeftLine, RightLine),
                    End2, NextLine, ResLine, V2, VarOut)
    ).

% L->-> : Special G4 rule
fitch_g4_proof(ltoto((Premisses > _), SP1, SP2), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    select(((Ant => Inter) => Cons), Premisses, _),
    find_context_line(((Ant => Inter) => Cons), Context, ComplexLine),
    
    % ETAPE 1 : Deriver (Inter => Cons) par L->->
    ExtractLine is CurLine + 1,
    format(atom(ExtractJust), 'L$ \\to \\to $ ~w', [ComplexLine]),
    render_have(Scope, (Inter => Cons), ExtractJust, CurLine, ExtractLine, VarIn, V1),
    assert_safe_fitch_line(ExtractLine, (Inter => Cons), ltoto(ComplexLine), Scope),
    
    % ETAPE 2 : Assumer Ant
    AssLine is ExtractLine + 1,
    assert_safe_fitch_line(AssLine, Ant, assumption, Scope),
    render_hypo(Scope, Ant, 'AS', ExtractLine, AssLine, V1, V2),
    NewScope is Scope + 1,
    
    % ETAPE 3 : Prouver Inter avec [Ant, (Inter=>Cons) | Context]
    fitch_g4_proof(SP1, [AssLine:Ant, ExtractLine:(Inter => Cons)|Context],
                  NewScope, AssLine, SubEnd, InterLine, V2, V3),
    
    % ETAPE 4 : Deriver (Ant => Inter) par ->I
    ImpLine is SubEnd + 1,
    assert_safe_fitch_line(ImpLine, (Ant => Inter), rcond(AssLine, InterLine), Scope),
    format(atom(Just1), '$ \\to I $ ~w-~w', [AssLine, InterLine]),
    render_have(Scope, (Ant => Inter), Just1, SubEnd, ImpLine, V3, V4),
    
    % ETAPE 5 : Deriver Cons par ->E
    MPLine is ImpLine + 1,
    assert_safe_fitch_line(MPLine, Cons, l0cond(ComplexLine, ImpLine), Scope),
    format(atom(Just2), '$ \\to E $ ~w,~w', [ComplexLine, ImpLine]),
    render_have(Scope, Cons, Just2, ImpLine, MPLine, V4, V5),
    
    % ETAPE 6 : Continuer avec SP2
    fitch_g4_proof(SP2, [MPLine:Cons, ImpLine:(Ant => Inter), ExtractLine:(Inter => Cons)|Context],
                  Scope, MPLine, NextLine, ResLine, V5, VarOut).
% =========================================================================
% REGLES DE QUANTIFICATION
% =========================================================================
% R?
fitch_g4_proof(rall((_ > [(![Z-X]:A)]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    fitch_g4_proof(SubProof, Context, Scope, CurLine, SubEnd, BodyLine, VarIn, V1),
    derive_formula(Scope, (![Z-X]:A), '$ \\forall I $ ~w', [BodyLine], rall(BodyLine),
                  SubEnd, NextLine, ResLine, V1, VarOut).
% L? : Elimination Universelle
fitch_g4_proof(lall((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    extract_new_formula(Premisses > _, SubProof, NewFormula),
    
    % Trouver le quantificateur universel qui genere NewFormula
    (
        % Cas 1: NewFormula est une instance directe d'un universel dans Premisses
        (
            member((![Z-X]:Body), Premisses),
            % Verifier si Body (avec substitution) donne NewFormula
            strip_annotations_deep(Body, StrippedBody),
            strip_annotations_deep(NewFormula, StrippedNew),
            unifiable(StrippedBody, StrippedNew, _),
            UniversalFormula = (![Z-X]:Body)
        ;
            % Cas 2: Chercher par structure equivalente
            member((![Z-X]:Body), Premisses),
            formulas_equivalent(Body, NewFormula),
            UniversalFormula = (![Z-X]:Body)
        ;
            % Cas 3: Fallback - prendre le premier (comportement actuel)
            select((![Z-X]:Body), Premisses, _),
            UniversalFormula = (![Z-X]:Body)
        )
    ),
    
    find_context_line(UniversalFormula, Context, UnivLine),
    derive_and_continue(Scope, NewFormula, '$ \\forall E $ ~w', [UnivLine], lall(UnivLine),
                       SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut).

% R?
fitch_g4_proof(rex((_ > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    fitch_g4_proof(SubProof, Context, Scope, CurLine, SubEnd, _WitnessLine, VarIn, V1),
    % ? CORRECTION : Referencer SubEnd (la ligne du temoin), pas WitnessLine
    derive_formula(Scope, Goal, '$ \\exists I $ ~w', [SubEnd], rex(SubEnd),
                  SubEnd, NextLine, ResLine, V1, VarOut).
% L?
fitch_g4_proof(lex((Premisses > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    select((?[Z-X]:Body), Premisses, _),
    find_context_line(?[Z-X]:Body, Context, ExistLine),
    extract_witness(SubProof, Witness),
    ( member(_:Witness, Context) ->
        fitch_g4_proof(SubProof, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut)
    ; WitLine is CurLine + 1,
      NewScope is Scope + 1,
      assert_safe_fitch_line(WitLine, Witness, assumption, NewScope),
      render_hypo(Scope, Witness, 'AS', CurLine, WitLine, VarIn, V1),
      fitch_g4_proof(SubProof, [WitLine:Witness|Context], NewScope, WitLine, SubEnd, _GoalLine, V1, V2),
      ElimLine is SubEnd + 1,
      assert_safe_fitch_line(ElimLine, Goal, lex(ExistLine, WitLine, SubEnd), Scope),
      % ? CORRECTION : Referencer SubEnd (derniere ligne de la sous-preuve)
      format(atom(Just), '$ \\exists E $ ~w,~w-~w', [ExistLine, WitLine, SubEnd]),
      render_have(Scope, Goal, Just, SubEnd, ElimLine, V2, VarOut),
      NextLine = ElimLine, ResLine = ElimLine
    ).
% L?? : Combined existential-disjunction 
fitch_g4_proof(lex_lor((_ > [Goal]), SP1, SP2), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    SP1 =.. [_, (Prem1 > _)|_],
    SP2 =.. [_, (Prem2 > _)|_],
    member(WitA, Prem1), contains_skolem(WitA), \+ is_quantified(WitA),
    member(WitB, Prem2), contains_skolem(WitB), \+ is_quantified(WitB),
    WitLine is CurLine + 1,
    render_hypo(Scope, (WitA | WitB), 'AS', CurLine, WitLine, VarIn, V1),
    NewScope is Scope + 1,
    assume_in_scope(WitA, Goal, SP1, [WitLine:(WitA | WitB)|Context],
                   NewScope, WitLine, EndA, GoalA, V1, V2),
    assume_in_scope(WitB, Goal, SP2, [WitLine:(WitA | WitB)|Context],
                   NewScope, EndA, EndB, GoalB, V2, V3),
    DisjElim is EndB + 1,
    CaseAStart is WitLine + 1,
    CaseBStart is EndA + 1,
    format(atom(DisjJust), '$ \\lor E $ ~w,~w-~w,~w-~w',
           [WitLine, CaseAStart, GoalA, CaseBStart, GoalB]),
    render_have(NewScope, Goal, DisjJust, EndB, DisjElim, V3, V4),
    ElimLine is DisjElim + 1,
    format(atom(ExistJust), '$ \\exists E $ ~w-~w', [WitLine, DisjElim]),
    render_have(Scope, Goal, ExistJust, DisjElim, ElimLine, V4, VarOut),
    NextLine = ElimLine, ResLine = ElimLine.

% CQ_c : Classical quantifier conversion
fitch_g4_proof(cq_c((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    extract_new_formula(Premisses, SubProof, NewFormula),
    select((![Z-X]:A) => B, Premisses, _),
    find_context_line((![Z-X]:A) => B, Context, Line),  % <- CORRECTION
    derive_and_continue(Scope, NewFormula, '$ CQ_{c} $ ~w', [Line], cq_c(Line),
                       SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut).

% CQ_m : Minimal quantifier conversion
fitch_g4_proof(cq_m((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    extract_new_formula(Premisses, SubProof, NewFormula),
    select((?[Z-X]:A)=>B, Premisses, _),
    find_context_line((?[Z-X]:A)=>B, Context, Line),  % <- CORRECTION : cherche la bonne ligne
    derive_and_continue(Scope, NewFormula, '$ CQ_{m} $ ~w', [Line], cq_m(Line),
                       SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut).

% =========================================================================
% REGLES D'EGALITE (EQUALITY RULES)
% =========================================================================
% =========================================================================
% REGLES D'EGALITE (EQUALITY RULES) - VERSION CORRIGEE
% =========================================================================

% Reflexivite
fitch_g4_proof(eq_refl(D), _Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    D = [Goal],
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, Goal, eq_refl, Scope),
    render_have(Scope, Goal, 'Leibniz', CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Symetrie
fitch_g4_proof(eq_sym(_G>D), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    D = [A = B],
    find_context_line(B = A, Context, EqLine),
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, (A = B), eq_sym(EqLine), Scope),
    format(atom(Just), 'Leibniz ~w', [EqLine]),
    render_have(Scope, (A = B), Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Transitivite
fitch_g4_proof(eq_trans(G>D), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    D = [A = C],
    G = [A = B, B = C | _Rest],  % Pattern matching direct
    find_context_line(A = B, Context, Line1),
    find_context_line(B = C, Context, Line2),
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, (A = C), eq_trans(Line1, Line2), Scope),
    format(atom(Just), 'Leibniz ~w,~w', [Line1, Line2]),
    render_have(Scope, (A = C), Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Substitution (Leibniz) - CAS PRINCIPAL
fitch_g4_proof(eq_subst(G>D), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    D = [Goal],
    Goal \= (_ = _),  % Pas une egalite
    
    % Extraire l'egalite et le predicat de G
    member(A = B, G),
    member(Pred, G),
    Pred \= (_ = _),
    Pred \= (A = B),
    
    % Verifier que Goal est Pred avec A remplace par B
    Pred =.. [PredName|Args],
    Goal =.. [PredName|GoalArgs],
    
    % Trouver la position ou la substitution a lieu
    nth0(Pos, Args, A),
    nth0(Pos, GoalArgs, B),
    
    % Trouver les numeros de ligne dans le contexte
    find_context_line(A = B, Context, EqLine),
    find_context_line(Pred, Context, PredLine),
    
    !,
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, Goal, eq_subst(EqLine, PredLine), Scope),
    format(atom(Just), 'Leibniz ~w,~w', [EqLine, PredLine]),
    render_have(Scope, Goal, Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Congruence
fitch_g4_proof(eq_cong(_G>D), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    D = [LHS = RHS],
    LHS =.. [F|ArgsL],
    RHS =.. [F|ArgsR],
    find_diff_pos(ArgsL, ArgsR, _Pos, TermL, TermR),
    find_context_line(TermL = TermR, Context, EqLine),
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, (LHS = RHS), eq_cong(EqLine), Scope),
    format(atom(Just), 'Leibniz ~w', [EqLine]),
    render_have(Scope, (LHS = RHS), Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Substitution dans egalite
fitch_g4_proof(eq_subst_eq(G>D), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    D = [Goal_LHS = Goal_RHS],
    member(X = Y, G),
    member(Ctx_LHS = Ctx_RHS, G),
    find_context_line(X = Y, Context, XY_Line),
    find_context_line(Ctx_LHS = Ctx_RHS, Context, Ctx_Line),
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, (Goal_LHS = Goal_RHS), eq_subst_eq(XY_Line, Ctx_Line), Scope),
    format(atom(Just), 'Leibniz ~w,~w', [XY_Line, Ctx_Line]),
    render_have(Scope, (Goal_LHS = Goal_RHS), Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Transitivite en chaine
fitch_g4_proof(eq_trans_chain(_G>D), _Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    D = [A = C],
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, (A = C), eq_trans_chain, Scope),
    render_have(Scope, (A = C), 'Leibniz', CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.
% =========================================================================
% FALLBACK
% =========================================================================
fitch_g4_proof(UnknownRule, _Context, _Scope, CurLine, CurLine, CurLine, VarIn, VarIn) :-
    format('% WARNING: Unknown rule ~w~n', [UnknownRule]).
% =========================================================================
%  END of FITCH PRINTER 
% =========================================================================
% =========================================================================
% NATURAL DEDUCTION PRINTER IN TREE STYLE  
% =========================================================================
% =========================================================================
% DISPLAY PREMISS FOR TREE STYLE 
% =========================================================================
% render_premise_list_silent/5: Silent version for tree style
render_premise_list_silent([], _, Line, Line, []) :- !.

render_premise_list_silent([LastPremiss], Scope, CurLine, NextLine, [CurLine:LastPremiss]) :-
    !,
    assert_safe_fitch_line(CurLine, LastPremiss, premise, Scope),
    NextLine is CurLine + 1.

render_premise_list_silent([Premiss|Rest], Scope, CurLine, NextLine, [CurLine:Premiss|RestContext]) :-
    assert_safe_fitch_line(CurLine, Premiss, premise, Scope),
    NextCurLine is CurLine + 1,
    render_premise_list_silent(Rest, Scope, NextCurLine, NextLine, RestContext).

% =========================================================================
% INTERFACE TREE STYLE
% =========================================================================
render_nd_tree_proof(Proof) :-
    retractall(fitch_line(_, _, _, _)),
    retractall(abbreviated_line(_)),
    extract_formula_from_proof(Proof, TopFormula),
    detect_and_set_logic_level(TopFormula),
    catch(
        (
            ( premise_list(PremissList), PremissList = [_|_] ->
                render_premise_list_silent(PremissList, 0, 1, NextLine, InitialContext),
                LastPremLine is NextLine - 1,
                % Capture ResLine (6ème argument) qui est la ligne de conclusion
                with_output_to(atom(_), fitch_g4_proof(Proof, InitialContext, 1, LastPremLine, _, _ResLine, 0, _)),
                
                % FIX: Trouver la dernière ligne qui N'EST PAS une prémisse
                findall(N, (fitch_line(N, _, Just, _), Just \= premise), DerivedLines),
                ( DerivedLines = [] ->
                    % Pas de ligne dérivée, utiliser la dernière prémisse (cas axiome pur)
                    RootLine = LastPremLine
                ;
                    % Utiliser la dernière ligne dérivée
                    max_list(DerivedLines, RootLine)
                )
            ;
                % Pas de prémisses
                with_output_to(atom(_), fitch_g4_proof(Proof, [], 1, 0, _, ResLine, 0, _)),
                RootLine = ResLine
            ),
            % Utilisation de RootLine comme racine de l'arbre
            collect_and_render_tree(RootLine)
        ),
        Error,
        (
            format('% Error rendering ND tree: ~w~n', [Error]),
            write('% Skipping tree visualization'), nl
        )
    ).

% =========================================================================
% COLLECT AND RENDER TREE
% =========================================================================

collect_and_render_tree(RootLineNum) :-
    findall(N-Formula-Just-Scope, 
            (fitch_line(N, Formula, Just, Scope), \+ abbreviated_line(N)), 
            Lines),
    predsort(compare_lines, Lines, SortedLines),
    ( SortedLines = [] ->
        write('% Empty proof tree'), nl
    ;
        % Capture toutes les formules prémisses pour le wrapping conditionnel
        findall(F, fitch_line(_, F, premise, _), AllPremises),

        ( build_buss_tree(RootLineNum, SortedLines, Tree) ->
            
            % Vérifie si la conclusion est simple (premisse/reiteration) ET qu'il y a plusieurs prémisses
            % FIX: Check RootLineNum for justification, not just any line.
            ( is_simple_conclusion(RootLineNum, AllPremises) ->
                % Force la structure pour afficher TOUTES les prémisses comme branches
                wrap_premises_in_tree(RootLineNum, AllPremises, FinalTree)
            ;
                FinalTree = Tree
            ),
            
            write('\\begin{prooftree}'), nl,
            render_buss_tree(FinalTree),
            write('\\end{prooftree}'), nl
        ;
            write('% Warning: missing referenced line(s) or broken tree structure'), nl
        )
    ).

compare_lines(Delta, N1-_-_-_, N2-_-_-_) :-
    compare(Delta, N1, N2).

% Helper pour vérifier si la conclusion est une simple réitération ou une prémisse
% FIX: Ensures the justification check is for the RootLineNum.
is_simple_conclusion(RootLineNum, AllPremises) :-
    length(AllPremises, N),
    N > 1, % Doit avoir plusieurs prémisses
    fitch_line(RootLineNum, _, Just, _), % Check RootLineNum's justification
    ( Just = premise ; Just = reiteration(_) ),
    !.

% Helper pour forcer la création d'un nœud n-aire de prémisses
wrap_premises_in_tree(RootLineNum, AllPremises, FinalTree) :-
    % Crée une liste de premise_node(F) pour toutes les prémisses
    findall(premise_node(F), member(F, AllPremises), PremiseTrees),
    % Obtient la formule de conclusion
    fitch_line(RootLineNum, FinalFormula, _, _),
    
    % Crée le nœud forcé
    FinalTree = n_ary_premise_node(FinalFormula, PremiseTrees).

% =========================================================================
% CONSTRUCTION D'ARBRE BUSSPROOFS
% =========================================================================

build_buss_tree(LineNum, FitchLines, Tree) :-
    ( member(LineNum-Formula-Just-_Scope, FitchLines) ->
        build_tree_from_just(Just, LineNum, Formula, FitchLines, Tree)
    ;
        fail
    ).

% -- Réitération (Règle déplacée pour priorité, corrige P, Q |- P) --
build_tree_from_just(reiteration(SourceLine), _LineNum, Formula, FitchLines, reiteration_node(Formula, SubTree)) :-
    !,
    build_buss_tree(SourceLine, FitchLines, SubTree).

% -- Feuilles --
build_tree_from_just(assumption, LineNum, Formula, _FitchLines, assumption_node(Formula, LineNum)) :- !.
build_tree_from_just(axiom, _LineNum, Formula, _FitchLines, axiom_node(Formula)) :- !.
build_tree_from_just(premise, _LineNum, Formula, _FitchLines, premise_node(Formula)) :- !.

% -- Règles Implication --
% R->
build_tree_from_just(rcond(HypNum, GoalNum), _LineNum, Formula, FitchLines, discharged_node(rcond, HypNum, Formula, SubTree)) :-
    !, build_buss_tree(GoalNum, FitchLines, SubTree).

% L0-> (Modus Ponens)
build_tree_from_just(l0cond(MajLine, MinLine), _LineNum, Formula, FitchLines, binary_node(l0cond, Formula, TreeA, TreeB)) :-
    !, build_buss_tree(MajLine, FitchLines, TreeA), build_buss_tree(MinLine, FitchLines, TreeB).

% L->-> (Règle spéciale G4)
build_tree_from_just(ltoto(Line), _LineNum, Formula, FitchLines, unary_node(ltoto, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% -- Règles Disjonction --
% R? (Intro Or)
build_tree_from_just(ror(SubLine), _LineNum, Formula, FitchLines, unary_node(ror, Formula, SubTree)) :-
    !, build_buss_tree(SubLine, FitchLines, SubTree).

% L? (Elim Or) - Ternaire
build_tree_from_just(lor(DisjLine, HypA, HypB, GoalA, GoalB), _LineNum, Formula, FitchLines,
                     ternary_node(lor, HypA, HypB, Formula, DisjTree, TreeA, TreeB)) :-
    !, build_buss_tree(DisjLine, FitchLines, DisjTree),
    build_buss_tree(GoalA, FitchLines, TreeA),
    build_buss_tree(GoalB, FitchLines, TreeB).

% L?-> (Disjonction gauche vers flèche)
build_tree_from_just(lorto(Line), _LineNum, Formula, FitchLines, unary_node(lorto, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% -- Règles Conjonction --
% L? (Elim And)
build_tree_from_just(land(ConjLine, _Which), _LineNum, Formula, FitchLines, unary_node(land, Formula, SubTree)) :-
    !, build_buss_tree(ConjLine, FitchLines, SubTree).
build_tree_from_just(land(ConjLine), _LineNum, Formula, FitchLines, unary_node(land, Formula, SubTree)) :-
    !, build_buss_tree(ConjLine, FitchLines, SubTree).

% R? (Intro And)
build_tree_from_just(rand(LineA, LineB), _LineNum, Formula, FitchLines, binary_node(rand, Formula, TreeA, TreeB)) :-
    !, build_buss_tree(LineA, FitchLines, TreeA), build_buss_tree(LineB, FitchLines, TreeB).

% L?-> (Conjonction gauche vers flèche)
build_tree_from_just(landto(Line), _LineNum, Formula, FitchLines, unary_node(landto, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% -- Règles Falsum / Négation --
% L? (Bot Elim)
build_tree_from_just(lbot(BotLine), _LineNum, Formula, FitchLines, unary_node(lbot, Formula, SubTree)) :-
    !, build_buss_tree(BotLine, FitchLines, SubTree).

% IP (Preuve indirecte / Classique)
build_tree_from_just(ip(HypNum, BotNum), _LineNum, Formula, FitchLines, discharged_node(ip, HypNum, Formula, SubTree)) :-
    !, build_buss_tree(BotNum, FitchLines, SubTree).

% -- Règles Quantificateurs --
% L? (Exist Elim)
build_tree_from_just(lex(ExistLine, WitNum, GoalNum), _LineNum, Formula, FitchLines, 
                     discharged_node(lex, WitNum, Formula, ExistTree, GoalTree)) :-
    !,
    build_buss_tree(ExistLine, FitchLines, ExistTree), build_buss_tree(GoalNum, FitchLines, GoalTree).

% R? (Exist Intro)
build_tree_from_just(rex(WitLine), _LineNum, Formula, FitchLines, unary_node(rex, Formula, SubTree)) :-
    !, build_buss_tree(WitLine, FitchLines, SubTree).

% L? (Forall Elim)
build_tree_from_just(lall(UnivLine), _LineNum, Formula, FitchLines, unary_node(lall, Formula, SubTree)) :-
    !, build_buss_tree(UnivLine, FitchLines, SubTree).

% R? (Forall Intro)
build_tree_from_just(rall(BodyLine), _LineNum, Formula, FitchLines, unary_node(rall, Formula, SubTree)) :-
    !, build_buss_tree(BodyLine, FitchLines, SubTree).

% Conversions Quantificateurs
build_tree_from_just(cq_c(Line), _LineNum, Formula, FitchLines, unary_node(cq_c, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

build_tree_from_just(cq_m(Line), _LineNum, Formula, FitchLines, unary_node(cq_m, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% -- Règles d'Égalité --
build_tree_from_just(eq_refl, _LineNum, Formula, _FitchLines, axiom_node(Formula)) :- !.

build_tree_from_just(eq_sym(SourceLine), _LineNum, Formula, FitchLines, 
                     unary_node(eq_sym, Formula, SubTree)) :-
    !, build_buss_tree(SourceLine, FitchLines, SubTree).

build_tree_from_just(eq_trans(Line1, Line2), _LineNum, Formula, FitchLines, 
                     binary_node(eq_trans, Formula, Tree1, Tree2)) :-
    !, build_buss_tree(Line1, FitchLines, Tree1), build_buss_tree(Line2, FitchLines, Tree2).

build_tree_from_just(eq_subst(Line1, Line2), _LineNum, Formula, FitchLines,
                     binary_node(eq_subst, Formula, Tree1, Tree2)) :-
    !, build_buss_tree(Line1, FitchLines, Tree1), build_buss_tree(Line2, FitchLines, Tree2).

build_tree_from_just(eq_cong(SourceLine), _LineNum, Formula, FitchLines, 
                     unary_node(eq_cong, Formula, SubTree)) :-
    !, build_buss_tree(SourceLine, FitchLines, SubTree).

build_tree_from_just(eq_subst_eq(Line1, Line2), _LineNum, Formula, FitchLines,
                     binary_node(eq_subst_eq, Formula, Tree1, Tree2)) :-
    !, build_buss_tree(Line1, FitchLines, Tree1), build_buss_tree(Line2, FitchLines, Tree2).

build_tree_from_just(eq_trans_chain, _LineNum, Formula, _FitchLines, 
                     axiom_node(Formula)) :- !.

% Fallback
build_tree_from_just(Just, LineNum, Formula, _FitchLines, unknown_node(Just, LineNum, Formula)) :-
    format('% WARNING: Unknown justification type: ~w~n', [Just]).

% =========================================================================
% RENDU RECURSIF DE L'ARBRE (Latex Bussproofs)
% =========================================================================

% render_buss_tree(+Tree)
% Genere les commandes LaTeX pour l'arbre

% -- Feuilles --
render_buss_tree(axiom_node(F)) :-
    write('\\AxiomC{$'), render_formula_for_buss(F), write('$}'), nl.

render_buss_tree(premise_node(F)) :-
    write('\\AxiomC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- Hypothèses (STYLE CORRIGÉ: Numéro en petite taille, noLine, Formule) --
render_buss_tree(assumption_node(F, HypNum)) :-
    format('\\AxiomC{\\scriptsize{~w}}', [HypNum]), nl, % Ajout de \scriptsize
    write('\\noLine'), nl,
    write('\\UnaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- Réitération --
render_buss_tree(reiteration_node(F, SubTree)) :-
    render_buss_tree(SubTree),
    % Correction: Utilisation de write/nl pour s'assurer que l'inférence est rendue
    write('\\RightLabel{\\scriptsize{R}}'), nl,
    write('\\UnaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- Noeuds N-aires FORCÉS pour l'affichage de toutes les prémisses (cas simple conclusion) --
render_buss_tree(n_ary_premise_node(F, Trees)) :-
    % 1. Rendu de tous les sous-arbres (prémisses)
    maplist(render_buss_tree, Trees),
    
    % 2. Ajout de l'étiquette Wk (Weakening)
    write('\\RightLabel{\\scriptsize{Wk}}'), nl,
    
    % 3. Utilisation de BinaryInfC si N=2 (P et Q)
    length(Trees, N),
    ( N = 2 ->
        % La commande BinayInfC prend les deux dernières AxiomC, correspondant exactement à la demande P, Q |- P
        write('\\BinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl
    ;
        % Pour N > 2, nous utilisons TrinaryInfC si possible, sinon un message
        ( N = 3 ->
            write('\\TrinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl
        ;
            % Si N>3 (peu probable pour une preuve simple), on se rabat sur BinaryInfC pour garder le document compilable
            format('% Warning: Simplified N=~w inference to BinaryInfC for display.', [N]), nl,
            write('\\BinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl
        )
    ).

% -- Noeuds Unaires --
render_buss_tree(unary_node(Rule, F, SubTree)) :-
    render_buss_tree(SubTree),
    format_rule_label(Rule, Label),
    format('\\RightLabel{\\scriptsize{~w}}~n', [Label]),
    write('\\UnaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- Noeuds Binaires --
render_buss_tree(binary_node(Rule, F, TreeA, TreeB)) :-
    render_buss_tree(TreeA),
    render_buss_tree(TreeB),
    format_rule_label(Rule, Label),
    format('\\RightLabel{\\scriptsize{~w}}~n', [Label]),
    write('\\BinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.


% -- Noeuds Ternaires --
render_buss_tree(ternary_node(Rule, HypA, HypB, F, TreeA, TreeB, TreeC)) :-
    render_buss_tree(TreeA),
    render_buss_tree(TreeB),
    render_buss_tree(TreeC),
    format_rule_label(Rule, Label),
    ( Rule = lor -> 
        format('\\RightLabel{\\scriptsize{~w}~w,~w}~n', [Label, HypA, HypB])
    ; 
        format('\\RightLabel{\\scriptsize{~w}}~n', [Label])
    ),
    write('\\TrinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- Noeuds avec Déchargement (Hypothèses) --
render_buss_tree(discharged_node(Rule, HypNum, F, SubTree)) :-
    render_buss_tree(SubTree),
    format_rule_label(Rule, BaseLabel),
    % Indique l'indice de l'hypothèse déchargée à côté de la règle
    format('\\RightLabel{\\scriptsize{~w} ~w}', [BaseLabel, HypNum]), nl,
    write('\\UnaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% Cas spécial pour exists elimination
render_buss_tree(discharged_node(lex, WitNum, F, ExistTree, GoalTree)) :-
    render_buss_tree(ExistTree),
    render_buss_tree(GoalTree),
    format('\\RightLabel{\\scriptsize{$\\exists E$} ~w}', [WitNum]), nl,
    write('\\BinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% Fallback
render_buss_tree(unknown_node(Just, _, F)) :-
    write('\\AxiomC{?'), write(Just), write('?}'), nl,
    write('\\UnaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% =========================================================================
% HELPER: LABELS DES REGLES
% =========================================================================
format_rule_label(rcond, '$\\to I$').
format_rule_label(l0cond, '$\\to E$').
format_rule_label(ror, '$\\lor I$').
format_rule_label(lor, '$\\lor E$').
format_rule_label(land, '$\\land E$').
format_rule_label(rand, '$\\land I$').
format_rule_label(lbot, '$\\bot E$').
format_rule_label(ip, 'IP').
format_rule_label(lex, '$\\exists E$').
format_rule_label(rex, '$\\exists I$').
format_rule_label(lall, '$\\forall E$').
format_rule_label(rall, '$\\forall I$').
format_rule_label(ltoto, '$L\\to\\to$').
format_rule_label(landto, '$L\\land\\to$').
format_rule_label(lorto, '$L\\lor\\to$').
format_rule_label(cq_c, '$CQ_c$').
format_rule_label(cq_m, '$CQ_m$').
format_rule_label(eq_refl, 'Refl').
format_rule_label(eq_sym, 'Sym').
format_rule_label(eq_trans, 'Trans').
format_rule_label(eq_subst, '$ Leibniz $').
format_rule_label(eq_cong, 'Cong').
format_rule_label(eq_subst_eq, 'SubstEq').
format_rule_label(X, X). % Fallback

%========================================================================
% END OF TREE STYLE PRINTER
%========================================================================

% =========================================================================
% HELPER: WRAPPER POUR REWRITE
% =========================================================================
% CORRIGE: Utilise write_formula_with_parens/1 pour gerer correctement
% le parenthesage des formules complexes dans les conditionnels.
% Exemple: (P & Q) -> R  et non  P & Q -> R
render_formula_for_buss(F) :-
    rewrite(F, 0, _, Latex),
    write_formula_with_parens(Latex).

render_formula_for_buss(Formula) :-
    catch(
        (rewrite(Formula, 0, _, LatexFormula), render_latex_formula(LatexFormula)),
        _Error,
        (write('???'))
    ).


% Helper : detecter un arbre d'egalite
is_equality_tree(binary_node(eq_subst, _, _, _)) :- !.
is_equality_tree(binary_node(eq_trans, _, _, _)) :- !.
is_equality_tree(binary_node(eq_subst_eq, _, _, _)) :- !.
is_equality_tree(unary_node(eq_sym, _, _)) :- !.
is_equality_tree(unary_node(eq_cong, _, _)) :- !.
is_equality_tree(axiom_node(_)) :- !.

all_premises_used(_, []) :- !.
all_premises_used(Tree, [P|Ps]) :-
    tree_contains_formula(Tree, P),
    all_premises_used(Tree, Ps).

% Helper : enlever les annotations de variables
strip_annotations(![_-X]:Body, ![X]:StrippedBody) :- 
    !, strip_annotations(Body, StrippedBody).
strip_annotations(?[_-X]:Body, ?[X]:StrippedBody) :- 
    !, strip_annotations(Body, StrippedBody).
strip_annotations(A & B, SA & SB) :- 
    !, strip_annotations(A, SA), strip_annotations(B, SB).
strip_annotations(A | B, SA | SB) :- 
    !, strip_annotations(A, SA), strip_annotations(B, SB).
strip_annotations(A => B, SA => SB) :- 
    !, strip_annotations(A, SA), strip_annotations(B, SB).
strip_annotations(A <=> B, SA <=> SB) :- 
    !, strip_annotations(A, SA), strip_annotations(B, SB).
strip_annotations(F, F).

% Matcher avec normalisation des annotations
tree_contains_formula(premise_node(F), P) :- 
    !,
    strip_annotations(F, F_stripped),
    strip_annotations(P, P_stripped),
    (F_stripped == P_stripped ; subsumes_term(F_stripped, P_stripped) ; subsumes_term(P_stripped, F_stripped)).

tree_contains_formula(axiom_node(F), P) :- 
    !,
    strip_annotations(F, F_stripped),
    strip_annotations(P, P_stripped),
    (F_stripped == P_stripped ; subsumes_term(F_stripped, P_stripped) ; subsumes_term(P_stripped, F_stripped)).

tree_contains_formula(hypothesis(_, F), P) :- 
    !,
    strip_annotations(F, F_stripped),
    strip_annotations(P, P_stripped),
    (F_stripped == P_stripped ; subsumes_term(F_stripped, P_stripped) ; subsumes_term(P_stripped, F_stripped)).

tree_contains_formula(unary_node(_, _, SubTree), F) :- 
    tree_contains_formula(SubTree, F).
tree_contains_formula(binary_node(_, _, TreeA, TreeB), F) :-
    (tree_contains_formula(TreeA, F) ; tree_contains_formula(TreeB, F)).
tree_contains_formula(ternary_node(_, _, _, _, TreeA, TreeB, TreeC), F) :-
    (tree_contains_formula(TreeA, F) ; tree_contains_formula(TreeB, F) ; tree_contains_formula(TreeC, F)).
tree_contains_formula(discharged_node(_, _, _, SubTree), F) :-
    tree_contains_formula(SubTree, F).
tree_contains_formula(discharged_node(_, _, _, TreeA, TreeB), F) :-
    (tree_contains_formula(TreeA, F) ; tree_contains_formula(TreeB, F)).


% =======================
% Fitch section
% ========================

% =========================================================================
% RENDERING PRIMITIVES
% =========================================================================

% render_hypo/7: Affiche une hypothese en Fitch style

render_hypo(Scope, Formula, Label, _CurLine, _NextLine, VarIn, VarOut) :-
    render_fitch_indent(Scope),
    write(' \\fh '),
    rewrite(Formula, VarIn, VarOut, LatexFormula),
    write_formula_with_parens(LatexFormula),
    write(' &  '),
    write(Label),
    write('\\\\'), nl.


% render_fitch_indent/1: Genere l'indentation Fitch (\\fa)

render_fitch_indent(0) :- !.

render_fitch_indent(N) :- 
    N > 0,
    write('\\fa '),
    N1 is N - 1,
    render_fitch_indent(N1).

render_have(Scope, Formula, Just, _CurLine, _NextLine, VarIn, VarOut) :-
    render_fitch_indent(Scope),
    % Toujours ecrire \fa au niveau 0 (pour les sequents)
    ( Scope = 0 -> write('\\fa ') ; true ),
    rewrite(Formula, VarIn, VarOut, LatexFormula),
    write_formula_with_parens(LatexFormula),
    write(' &  '),
    write(Just),
    write('\\\\'), nl.
 
render_lineno(J, K) :-
   K is J+1.

render_bars(0) :- !.
render_bars(N) :-
    write('\\fa  '),
    M is N-1,
    render_bars(M).

render_label(L) :-
    L =.. ['$ \\lor E $', DisjLine, Case1, Case2],
    Case1 = (Start1-End1),
    Case2 = (Start2-End2),
    !,
    write(' & '),
    format(' $ \\lor E $ ~w,~w-~w,~w-~w', [DisjLine, Start1, End1, Start2, End2]),
    write('\\'), write('\\\n').

render_label(L) :-
    L =.. [F,X,Y],
    !,
    write(' &  '),
    write(' '),
    write(F),
    write(' '),
    write(X),
    write(', '),
    write(Y),
    write('\\'), write('\\\n').

render_label(L) :-
    L =.. [F,X],
    !,
    write(' & '),
    write(' '),
    write(F),
    write(' '),
    write(X),
    write('\\'), write('\\\n').

render_label(L) :-
    !,
    write(' & '),
    write(' '),
    write(L),
    write('\\'), write('\\\n').

% =========================================================================
% REGLE SIMPLE : (Antecedent) => (Consequent) sauf pour les atomes
% =========================================================================

% Test si une formule est atomique
is_atomic_formula(Formula) :-
    atomic(Formula).

% -------------------------------------------------------------------------
% NOUVEAU : Test si une formule est une negation (au sens de l'affichage LaTeX)
% Une formule negative est representee comme (' \\lnot ' X) par rewrite/4.
% Nous voulons considerer toute formule commencant par ' \\lnot ' comme
% "non-parenthesable" - i.e. ne PAS entourer par des parentheses externe.
% -------------------------------------------------------------------------
is_negative_formula((' \\lnot ' _)) :- !.

% Helper: treat negative formulas as "atomic-like" for parentheses suppression
is_atomic_or_negative_formula(F) :-
    is_atomic_formula(F) ;
    is_negative_formula(F).

% =========================================================================
% TEST SI LE CORPS D'UN QUANTIFICATEUR NECESSITE PARENTHESES
% =========================================================================

quantifier_body_needs_parens((_ ' \\to ' _)) :- !.
quantifier_body_needs_parens((_ ' \\land ' _)) :- !.
quantifier_body_needs_parens((_ ' \\lor ' _)) :- !.
quantifier_body_needs_parens((_ ' \\leftrightarrow ' _)) :- !.
quantifier_body_needs_parens(_) :- fail.


quantifier_body_needs_parens(Body) :-
    (Body = (_ ' \\to ' _)
    ; Body = (_ ' \\land ' _) 
    ; Body = (_ ' \\lor ' _)
    ; Body = (_ ' \\leftrightarrow ' _)
    ).
% =========================================================================
% TOUTES LES CLAUSES DE write_formula_with_parens/1 GROUPEES
% =========================================================================

% Ecriture d'une implication avec parentheses intelligentes
write_formula_with_parens((A ' \\to ' B)) :-
    !,
    write_implication_with_parens(A, B).

write_formula_with_parens('='(A, B)) :- !,
    write('('), write_formula_with_parens(A), write(' = '), write_formula_with_parens(B), write(')').

% Autres operateurs
write_formula_with_parens((A ' \\lor ' B)) :-
    !,
    write_with_context(A, 'lor_left'),
    write(' \\lor '),
    write_with_context(B, 'lor_right').

write_formula_with_parens((A ' \\land ' B)) :-
    !,
    write_with_context(A, 'land_left'),
    write(' \\land '),
    write_with_context(B, 'land_right').

write_formula_with_parens((A ' \\leftrightarrow ' B)) :-
    !,
    write_with_context(A, 'equiv_left'),
    write(' \\leftrightarrow '),
    write_with_context(B, 'equiv_right').

write_formula_with_parens((' \\lnot ' A)) :-
    !,
    write(' \\lnot '),
    write_with_context(A, 'not').

% QUANTIFICATEURS AVEC PARENTHESES INTELLIGENTES
write_formula_with_parens((' \\forall ' X ' ' A)) :-
    !,
    write(' \\forall '),
    write(X),
    write(' '),
    ( quantifier_body_needs_parens(A) ->
        write('('),
        write_formula_with_parens(A),
        write(')')
    ;   write_formula_with_parens(A)
    ).

write_formula_with_parens((' \\exists ' X ' ' A)) :-
    !,
    write(' \\exists '),
    write(X),
    write(' '),
    ( quantifier_body_needs_parens(A) ->
        write('('),
        write_formula_with_parens(A),
        write(')')
    ;   write_formula_with_parens(A)
    ).

write_formula_with_parens(Other) :-
    write(Other).

% =========================================================================
% FONCTION SPECIALISEE POUR IMPLICATIONS
% =========================================================================

write_implication_with_parens(Antecedent, Consequent) :-
    % Antecedent : ne pas parentheser s'il est atomique OU une formule negative
    ( is_atomic_or_negative_formula(Antecedent) ->
        write_formula_with_parens(Antecedent)
    ;
        write('('),
        write_formula_with_parens(Antecedent),
        write(')')
    ),
    write(' \\to '),
    % Consequent : parentheser sauf si atomique OU formule negative
    % NOTE: on considere toute forme (' \\lnot ' _) comme "negative" meme si
    % elle contient plusieurs negations imbriquees (!!!A). Dans ce cas on ne
    % met JAMAIS de parentheses externes autour de la negation.
    ( is_atomic_or_negative_formula(Consequent) ->
        write_formula_with_parens(Consequent)
    ;
        write('('),
        write_formula_with_parens(Consequent),
        write(')')
    ).

% =========================================================================
% TOUTES LES CLAUSES DE write_with_context/2 GROUPEES
% =========================================================================

% IMPLICATIONS dans tous les contextes - utiliser write_implication_with_parens
write_with_context((A ' \\to ' B), 'lor_left') :-
    !,
    write('('),
    write_implication_with_parens(A, B),
    write(')').

write_with_context((A ' \\to ' B), 'lor_right') :-
    !,
    write('('),
    write_implication_with_parens(A, B),
    write(')').

write_with_context((A ' \\to ' B), 'land_left') :-
    !,
    write('('),
    write_implication_with_parens(A, B),
    write(')').

write_with_context((A ' \\to ' B), 'land_right') :-
    !,
    write('('),
    write_implication_with_parens(A, B),
    write(')').

write_with_context((A ' \\to ' B), 'not') :-
    !,
    write('('),
    write_implication_with_parens(A, B),
    write(')').

% CONJONCTIONS dans disjonctions
write_with_context((A ' \\land ' B), 'lor_left') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\land '),
    write_formula_with_parens(B),
    write(')').

write_with_context((A ' \\land ' B), 'lor_right') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\land '),
    write_formula_with_parens(B),
    write(')').

% CONJONCTIONS dans negations
write_with_context((A ' \\land ' B), 'not') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\land '),
    write_formula_with_parens(B),
    write(')').

% DISJONCTIONS dans negations
write_with_context((A ' \\lor ' B), 'not') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\lor '),
    write_formula_with_parens(B),
    write(')').

% DISJONCTIONS dans conjonctions
write_with_context((A ' \\lor ' B), 'land_left') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\lor '),
    write_formula_with_parens(B),
    write(')').

write_with_context((A ' \\lor ' B), 'land_right') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\lor '),
    write_formula_with_parens(B),
    write(')').

% CLAUSE DE FALLBACK
write_with_context(Formula, _Context) :-
    write_formula_with_parens(Formula).

% =========================================================================
% SYSTEME BURSE adapte : rewrite direct sur formules avec operateurs standard
% VERSION AVEC SIMPLIFICATION ELEGANTE DES PREDICATS
% =========================================================================

% rewrite/4 - Version adaptee qui gere directement les formules
rewrite(#, J, J, '\\bot') :- !.
rewrite(# => #, J, J, '\\top') :- !.

% NOUVELLE CLAUSE POUR GERER LES CONSTANTES DE SKOLEM
% Convertit f_sk(K,_) en un nom simple comme 'a', 'b', etc.
rewrite(f_sk(K,_), J, J, Name) :-
    !,
    rewrite_name(K, Name).

% CAS DE BASE : formules atomiques
rewrite(A, J, J, A_latex) :-
    atomic(A),
    !,
    toggle(A, A_latex).

% Reconnait ((A => B) & (B => A)) (ou l'ordre inverse) comme A <=> B pour l'affichage LaTeX
% Doit etre place AVANT la clause generique rewrite((A & B), ...)
rewrite((X & Y), J, K, (C ' \\leftrightarrow ' D)) :-
    % cas 1 : X = (A => B), Y = (B => A)
    ( X = (A => B), Y = (B => A)
    % cas 2 : ordre inverse
    ; X = (B => A), Y = (A => B)
    ),
    !,
    rewrite(A, J, H, C),
    rewrite(B, H, K, D).

% Conjonction avec operateur standard &
rewrite((A & B), J, K, (C ' \\land ' D)) :-
    !,
    rewrite(A, J, H, C),
    rewrite(B, H, K, D).

% Disjonction avec operateur standard |
rewrite((A | B), J, K, (C ' \\lor ' D)) :-
    !,
    rewrite(A, J, H, C),
    rewrite(B, H, K, D).

% AFFICHAGE COSMETIQUE : A => # devient !A
rewrite((A => #), J, K, (' \\lnot ' C)) :-
    !,
    rewrite(A, J, K, C).


% Implication avec operateur standard =>
rewrite((A => B), J, K, (C ' \\to ' D)) :-
    !,
    rewrite(A, J, H, C),
    rewrite(B, H, K, D).

% Biconditionnelle avec operateur standard <=>
rewrite((A <=> B), J, K, (C ' \\leftrightarrow ' D)) :-
    !,
    rewrite(A, J, H, C),
    rewrite(B, H, K, D).

% Negation avec operateur standard ~
rewrite((~A), J, K, (' \\lnot ' C)) :-
    !,
    rewrite(A, J, K, C).


% QUANTIFICATEURS : Version Burse pour format X-Y
rewrite((![X-X]:A), J, K, (' \\forall ' X ' ' C)) :-
    !,
    rewrite(A, J, K, C).

rewrite((?[X-X]:A), J, K, (' \\exists ' X ' ' C)) :-
    !,
    rewrite(A, J, K, C).
/*
% QUANTIFICATEURS : Adapter les formules directement
rewrite((![_X]:A), J, K, (' \\forall ' VarName ' ' C)) :-
    !,
    rewrite_name(J, VarName),
    J1 is J + 1,
    rewrite(A, J1, K, C).

rewrite((?[_X]:A), J, K, (' \\exists ' VarName ' ' C)) :-
    !,
    rewrite_name(J, VarName),
    J1 is J + 1,
    rewrite(A, J1, K, C).
*/
rewrite((![X]:A), J, K, (' \\forall ' X ' ' C)) :-
    !,
    rewrite(A, J, K, C).  % Garder le même compteur

rewrite((?[X]:A), J, K, (' \\exists ' X ' ' C)) :-
    !,
    rewrite(A, J, K, C).  % Garder le même compteur
% =========================================================================
% SIMPLIFICATION ELEGANTE DES PREDICATS
% P(x,y,z) -> Pxyz pour tous les predicats
% =========================================================================
/*
rewrite(Pred, J, K, SimplePred) :-
    Pred =.. [F|Args],
    atom(F),
    Args \= [],
    all_simple_terms(Args),
    !,
    toggle(F, G),
    rewrite_args_list(Args, J, K, SimpleArgs),
    concatenate_all([G|SimpleArgs], SimplePred).
*/

% --- Replace the previous "concatenate predicate name and args" clause by this safer version.
% We avoid applying this cosmetic concatenation to equality and other logical operators.
rewrite(Pred, J, K, SimplePred) :-
    Pred =.. [F|Args],
    atom(F),
    Args \= [],
    % Do NOT collapse standard logical operators or equality into a single atom:
    % exclude '=' and the main logical connectives (=>, <=>, &, |, ~)
    \+ member(F, ['=', '=>', '<=>', '&', '|', '~']),
    all_simple_terms(Args),
    !,
    toggle(F, G),
    rewrite_args_list(Args, J, K, SimpleArgs),
    concatenate_all([G|SimpleArgs], SimplePred).

% PREDICATS ET TERMES (clause generale)
rewrite(X, J, K, Y) :-
    X =.. [F|L],
    toggle(F, G),
    rewrite_list(L, J, K, R),
    Y =.. [G|R].


% =========================================================================
% PREDICATS AUXILIAIRES POUR LA SIMPLIFICATION
% =========================================================================

all_simple_terms([]).
all_simple_terms([H|T]) :-
    simple_term(H),
    all_simple_terms(T).

simple_term(X) :-
    atomic(X), !.
simple_term(X) :-
    var(X), !.
simple_term(f_sk(_,_)) :-
    !.
simple_term(X) :-
    X =.. [F|Args],
    atom(F),
    Args \= [],
    length(Args, Len),
    Len =< 2,
    all_simple_terms(Args).

rewrite_args_list([], J, J, []).
rewrite_args_list([H|T], J, K, [RH|RT]) :-
    rewrite_term(H, J, TempJ, RH),
    rewrite_args_list(T, TempJ, K, RT).

concatenate_all([X], X) :-
    atomic(X), !.
concatenate_all([H|T], Result) :-
    length([H|T], Len),
    Len =< 5,
    !,
    concatenate_all_impl([H|T], Result).
concatenate_all(_, _) :-
    fail.

concatenate_all_impl([X], X) :-
    atomic(X), !.
concatenate_all_impl([H|T], Result) :-
    concatenate_all_impl(T, TempResult),
    atom_concat(H, TempResult, Result).

% =========================================================================
% TRAITEMENT DES LISTES ET TERMES
% =========================================================================

rewrite_list([], J, J, []).
rewrite_list([X|L], J, K, [Y|R]) :-
    rewrite_term(X, J, H, Y),
    rewrite_list(L, H, K, R).

rewrite_term(V, J, K, V) :-
    var(V),
    !,
    rewrite_name(J, V),
    K is J+1.

rewrite_term(f_sk(K,_), J, J, N) :-
    !,
    rewrite_name(K, N).

% NOUVEAU : Si le terme est un atome simple (constante), NE PAS le capitaliser
% Car il est argument d'un predicat/fonction
rewrite_term(X, J, J, X) :-
    atomic(X),
    !.

rewrite_term(X, J, K, Y) :-
    X =.. [F|L],
    rewrite_list(L, J, K, R),
    Y =.. [F|R].

% Generateur de noms elegants
rewrite_name(K, N) :-
    K < 3,
    !,
    J is K+0'a,
    char_code(N, J).

rewrite_name(K, N) :-
    J is (K mod 3)+0'a,
    H is K div 3,
    number_codes(H, L),
    atom_codes(N, [J|L]).

% Toggle majuscules/minuscules
toggle(X, Y) :-
    atom_codes(X, L),
    toggle_list(L, R),
    atom_codes(Y, R).

toggle_list([], []).
toggle_list([X|L], [Y|R]) :-
    toggle_code(X, Y),
    toggle_list(L, R).

toggle_code(X, Y) :-
    0'a =< X, X =< 0'z,
    !,
    Y is X - 0'a + 0'A.

toggle_code(X, Y) :-
    0'A =< X, X =< 0'Z,
    !,
    Y is X - 0'A + 0'a.

toggle_code(X, X).

% =========================================================================
% SYSTEME PREPARE
% =========================================================================

prepare_sequent(PremisesList => Conclusion, PreparedPremises, PreparedConclusion) :-
    is_list(PremisesList),
    !,
    prepare_premises_list(PremisesList, PreparedPremises),
    prepare(Conclusion, [], PreparedConclusion).

prepare_sequent(Premises => Conclusion, [PreparedPremises], PreparedConclusion) :-
    prepare(Premises, [], PreparedPremises),
    prepare(Conclusion, [], PreparedConclusion).

prepare_premises_list([], []) :- !.
prepare_premises_list([H|T], [PreparedH|PreparedT]) :-
    prepare(H, [], PreparedH),
    prepare_premises_list(T, PreparedT).

prepare(#, _, #) :- !.

prepare((A & B), Q, (C & D)) :-
    !,
    prepare(A, Q, C),
    prepare(B, Q, D).

prepare((A | B), Q, (C | D)) :-
    !,
    prepare(A, Q, C),
    prepare(B, Q, D).

prepare((A => B), Q, (C => D)) :-
    !,
    prepare(A, Q, C),
    prepare(B, Q, D).

prepare((A <=> B), Q, (C <=> D)) :-
    !,
    prepare(A, Q, C),
    prepare(B, Q, D).

prepare((~A), Q, (~C)) :-
    !,
    prepare(A, Q, C).

prepare((![Z]:A), Q, (![Z-X]:C)) :-
    !,
    prepare(A, [Z-X|Q], C).

prepare((?[Z]:A), Q, (?[Z-X]:C)) :-
    !,
    prepare(A, [Z-X|Q], C).

prepare(X, _, X) :-
    var(X),
    !.

prepare(X, Q, Y) :-
    X =.. [F|L],
    prepare_list(L, Q, R),
    Y =.. [F|R].

prepare_term(X, _, X) :-
    var(X),
    !.

prepare_term(X, Q, Y) :-
    atom(X),
    member(X-Y, Q),
    !.

prepare_term(X, Q, Y) :-
    X =.. [F|L],
    prepare_list(L, Q, R),
    Y =.. [F|R].

prepare_list([], _, []).
prepare_list([X|L], Q, [Y|R]) :-
    prepare_term(X, Q, Y),
    prepare_list(L, Q, R).

% Support lambda calculus
lambda_has(V:_, W) :-
    V == W.

lambda_has(app(P,_,_,_), W) :-
    lambda_has(P, W).

lambda_has(app(_,Q,_,_), W) :-
    lambda_has(Q, W).

lambda_has(lam(V:_,_,_,_), W) :-
    V == W,
    !,
    fail.

lambda_has(lam(_,P,_,_), W) :-
    lambda_has(P, W).

lambda_has('C'(P,_,_), W) :-
    lambda_has(P, W).

%%%%%% Sequents

% Determiner le type de preuve (theoreme ou sequent)
% RENOMME pour eviter conflit avec proof_type/2 du driver
% Cette fonction analyse la STRUCTURE d'une preuve G4, pas la syntaxe d'une formule
proof_structure_type(Proof, Type) :-
    proof_premises(Proof, Premisses),
    (   Premisses = [] 
    ->  Type = theorem
    ;   Type = sequent
    ).

% NOTE: Si proof_structure_type est utilisee quelque part, mettre a jour les appels.
% Actuellement, elle ne semble appelee nulle part dans ce fichier.

% Generer les commandes Fitch selon le type et la position
fitch_prefix(sequent, LineNum, TotalPremisses, Prefix) :-
    (   LineNum =< TotalPremisses 
    ->  (   LineNum = TotalPremisses 
        ->  Prefix = '\\fj '  % Gros drapeau pour derniere premisse
        ;   Prefix = '\\fa '  % Ligne normale pour premisses
        )
    ;   Prefix = '\\fa '      % Ligne normale apres les premisses
    ).

fitch_prefix(theorem, Depth, _, Prefix) :-
    (   Depth > 0 
    ->  Prefix = '\\fa \\fh '  % Petit drapeau pour hypotheses
    ;   Prefix = '\\fa '       % Ligne normale au niveau 0
    ).

% =========================================================================
% RENDU LATEX BUSSPROOFS
% =========================================================================

% =========================================================================
% HELPERS POUR TREE RENDERING
% =========================================================================

hypothesis_is_discharged(HypNum, FitchLines) :-
    member(_-_-Just-_, FitchLines),
    justification_discharges(Just, HypNum).

justification_discharges(rcond(HypNum, _), HypNum) :- !.
justification_discharges(ip(HypNum, _), HypNum) :- !.
justification_discharges(lor(_, HypA, HypB, _, _), HypNum) :- (HypNum = HypA ; HypNum = HypB), !.
justification_discharges(lex(_, WitNum, _), WitNum) :- !.
justification_discharges(_, _) :- fail.

is_vacuous_discharge(HypNum, Tree, FitchLines) :-
    member(HypNum-Formula-assumption-_, FitchLines),
    \+ tree_uses_hypothesis(Tree, HypNum, Formula).

tree_uses_hypothesis(hypothesis(N, F), HypNum, HypFormula) :- N == HypNum, F =@= HypFormula.
tree_uses_hypothesis(unary_node(_, _, SubTree), HypNum, HypFormula) :- tree_uses_hypothesis(SubTree, HypNum, HypFormula).
tree_uses_hypothesis(binary_node(_, _, TreeA, TreeB), HypNum, HypFormula) :-
    ( tree_uses_hypothesis(TreeA, HypNum, HypFormula) ; tree_uses_hypothesis(TreeB, HypNum, HypFormula) ).
tree_uses_hypothesis(ternary_node(_, _, _, _, TreeA, TreeB, TreeC), HypNum, HypFormula) :-
    ( tree_uses_hypothesis(TreeA, HypNum, HypFormula) ; tree_uses_hypothesis(TreeB, HypNum, HypFormula) ; tree_uses_hypothesis(TreeC, HypNum, HypFormula) ).
tree_uses_hypothesis(discharged_node(_, _, _, SubTree), HypNum, HypFormula) :- tree_uses_hypothesis(SubTree, HypNum, HypFormula).
tree_uses_hypothesis(discharged_node(_, _, _, TreeA, TreeB), HypNum, HypFormula) :-
    ( tree_uses_hypothesis(TreeA, HypNum, HypFormula) ; tree_uses_hypothesis(TreeB, HypNum, HypFormula) ).

render_rule_name(ror) :- write('\\lor I').
render_rule_name(lbot) :- write('\\bot E').
render_rule_name(land) :- write('\\land E').
render_rule_name(rand) :- write('\\land I').
render_rule_name(rex) :- write('\\exists I').
render_rule_name(lall) :- write('\\forall E').
render_rule_name(rall) :- write('\\forall I').
render_rule_name(l0cond) :- write('\\to E').
render_rule_name(landto) :- write('L\\land\\to').
render_rule_name(lorto) :- write('L\\lor\\to').
render_rule_name(ltoto) :- write('L\\to\\to').
render_rule_name(cq_c) :- write('CQ_{c}').
render_rule_name(cq_m) :- write('CQ_{m}').
% Regles d'egalite -> Leibniz
render_rule_name(eq_subst) :- !, write('Leibniz').
render_rule_name(eq_trans) :- !, write('Leibniz').
render_rule_name(eq_subst_eq) :- !, write('Leibniz').
render_rule_name(eq_sym) :- !, write('Leibniz').
render_rule_name(eq_cong) :- !, write('Leibniz').
render_rule_name(eq_refl) :- !, write('Leibniz').
render_rule_name(eq_trans_chain) :- !, write('Leibniz').
% Fallback
render_rule_name(Rule) :- write(Rule).

% =========================================================================
% LaTeX FORMULA RENDERING
% =========================================================================

render_latex_formula((A ' \\to ' B)) :-
    !,
    ( is_atomic_or_negative_formula(A) ->
        render_latex_formula(A)
    ;
        write('('),
        render_latex_formula(A),
        write(')')
    ),
    write(' \\to '),
    ( is_atomic_or_negative_formula(B) ->
        render_latex_formula(B)
    ;
        write('('),
        render_latex_formula(B),
        write(')')
    ).

render_latex_formula((A ' \\land ' B)) :-
    !,
    render_latex_with_parens(A, 'conj_left'),
    write(' \\land '),
    render_latex_with_parens(B, 'conj_right').

render_latex_formula((A ' \\lor ' B)) :-
    !,
    render_latex_with_parens(A, 'disj_left'),
    write(' \\lor '),
    render_latex_with_parens(B, 'disj_right').

render_latex_formula((A ' \\leftrightarrow ' B)) :-
    !,
    write('('),
    render_latex_formula(A),
    write(' \\leftrightarrow '),
    render_latex_formula(B),
    write(')').

render_latex_formula('='(A, B)) :-
    !,
    write('('),
    render_latex_formula(A),
    write('='),
    render_latex_formula(B),
    write(')').

render_latex_formula((' \\lnot ' A)) :-
    !,
    write(' \\lnot '),
    render_latex_with_parens(A, 'neg').

render_latex_formula((' \\forall ' X ' ' A)) :-
    !,
    write(' \\forall '),
    write(X),
    write(' '),
    ( quantifier_body_needs_parens(A) ->
        write('('),
        render_latex_formula(A),
        write(')')
    ;
        render_latex_formula(A)
    ).

render_latex_formula((' \\exists ' X ' ' A)) :-
    !,
    write(' \\exists '),
    write(X),
    write(' '),
    ( quantifier_body_needs_parens(A) ->
        write('('),
        render_latex_formula(A),
        write(')')
    ;
        render_latex_formula(A)
    ).

render_latex_formula('\\bot') :-
    !,
    write('\\bot').

render_latex_formula(Atom) :-
    atomic(Atom),
    !,
    write(Atom).

render_latex_formula(Complex) :-
    write(Complex).

render_latex_with_parens((' \\lnot ' A), _Context) :-
    !,
    render_latex_formula((' \\lnot ' A)).

render_latex_with_parens((A ' \\to ' B), Context) :-
    needs_parens_in_context(' \\to ', Context),
    !,
    write('('),
    render_latex_formula((A ' \\to ' B)),
    write(')').

render_latex_with_parens((A ' \\land ' B), Context) :-
    needs_parens_in_context(' \\land ', Context),
    !,
    write('('),
    render_latex_formula((A ' \\land ' B)),
    write(')').

render_latex_with_parens((A ' \\lor ' B), Context) :-
    needs_parens_in_context(' \\lor ', Context),
    !, write('('),
    render_latex_formula((A ' \\lor ' B)), write(')').

render_latex_with_parens(Formula, _Context) :- render_latex_formula(Formula).

needs_parens_in_context(' \\to ', 'impl_left') :- !.
needs_parens_in_context(' \\to ', 'conj_left') :- !.
needs_parens_in_context(' \\to ', 'conj_right') :- !.
needs_parens_in_context(' \\to ', 'disj_left') :- !.
needs_parens_in_context(' \\to ', 'disj_right') :- !.
needs_parens_in_context(' \\to ', 'neg') :- !.
needs_parens_in_context(' \\land ', 'disj_left') :- !.
needs_parens_in_context(' \\land ', 'disj_right') :- !.
needs_parens_in_context(' \\land ', 'impl_left') :- !.
needs_parens_in_context(' \\land ', 'neg') :- !.
needs_parens_in_context(' \\lor ', 'conj_left') :- !.
needs_parens_in_context(' \\lor ', 'conj_right') :- !.
needs_parens_in_context(' \\lor ', 'impl_left') :- !.
needs_parens_in_context(' \\lor ', 'neg') :- !.
needs_parens_in_context(_, _) :- fail.
% =========================================================================
% END OF LATEX UTILITIES FILE
% =========================================================================
% =========================================================================
% LOGIC LEVEL DETECTION - Analyse holophrastique (Quine)
% Detection automatique : calcul propositionnel vs. calcul des predicats
% =========================================================================

:- dynamic formula_level/1.

% =========================================================================
% DETECTION PRINCIPALE
% =========================================================================

detect_and_set_logic_level(Formula) :-
    retractall(formula_level(_)),
    ( is_fol_formula(Formula) ->
        assertz(formula_level(fol))
    ;
        assertz(formula_level(propositional))
    ).

% =========================================================================
% HEURISTIQUES DE DETECTION FOL
% Une formule est FOL si elle contient :
% - Des quantificateurs (?, ?)
% - Des applications de predicats p(t1,...,tn) avec n > 0
% - Des egalites entre termes
% - Des fonctions de Skolem
% =========================================================================

is_fol_formula(Formula) :-
    (   contains_quantifier(Formula)
    ;   contains_predicate_application(Formula)  
    ;   contains_equality(Formula)
    ;   contains_function_symbol(Formula)
    ), !.

% =========================================================================
% DETECTION DES COMPOSANTS
% =========================================================================

% Quantificateurs
contains_quantifier(![_-_]:_) :- !.
contains_quantifier(?[_-_]:_) :- !.
contains_quantifier(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    contains_quantifier(Arg).


% Applications de predicats (termes composes qui ne sont pas des connecteurs)
contains_predicate_application(Term) :-
    compound(Term),
    \+ is_logical_connective_structure(Term),
    Term =.. [_F|Args],
    Args \= [],  % Doit avoir au moins un argument
    !.
contains_predicate_application(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    contains_predicate_application(Arg).

% Structures de connecteurs logiques (a exclure)
is_logical_connective_structure(_ => _).
is_logical_connective_structure(_ & _).
is_logical_connective_structure(_ | _).
is_logical_connective_structure(_ <=> _).
is_logical_connective_structure(_ = _).  % Egalite traitee separement
is_logical_connective_structure(~ _).
is_logical_connective_structure(#).
is_logical_connective_structure(![_-_]:_).
is_logical_connective_structure(?[_-_]:_).

% Egalite
contains_equality(_ = _) :- !.
contains_equality(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    contains_equality(Arg).

% Fonctions de Skolem
contains_function_symbol(f_sk(_,_)) :- !.
contains_function_symbol(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    contains_function_symbol(Arg).

% =========================================================================
% EXTRACTION DE LA FORMULE DEPUIS UNE PREUVE G4
% =========================================================================

extract_formula_from_proof(Proof, Formula) :-
    Proof =.. [_RuleName, Sequent|_],
    ( Sequent = (_ > [Formula]) -> 
        true
    ; Sequent = (_ > Goals), Goals = [Formula|_] -> 
        true
    ; 
        Formula = unknown
    ).
% =========================================================================
% VALIDATION & WARNINGS MODULE
% Detection of typing errors and misuse of logical operators
% =========================================================================
% This module validates formulas before proof attempt and warns about
% common mistakes, particularly the confusion between:
%   <=>  biconditional (propositional connective between formulas)
%   =    equality (relation between terms in FOL)
% =========================================================================


:- use_module(library(lists)).

% =========================================================================
% VALIDATION MODE CONFIGURATION
% =========================================================================
% Modes:
%   permissive - warn but continue (default)
%   strict     - reject invalid formulas automatically
%   silent     - no warnings

:- dynamic validation_mode/1.
validation_mode(permissive).

set_validation_mode(Mode) :-
    member(Mode, [permissive, strict, silent]),
    retractall(validation_mode(_)),
    assertz(validation_mode(Mode)).

% =========================================================================
% KNOWN PREDICATES REGISTRY
% =========================================================================
% Users can register predicate symbols to improve detection accuracy

:- dynamic known_predicate/1.

% Default predicates (common in logic examples)
known_predicate(p).
known_predicate(q).
known_predicate(r).
known_predicate(s).
known_predicate(h).
known_predicate(m).

register_predicate(P) :-
    \+ known_predicate(P),
    assertz(known_predicate(P)).

clear_predicates :-
    retractall(known_predicate(_)).

% =========================================================================
% MAIN VALIDATION ENTRY POINT
% =========================================================================

validate_and_warn(Formula, ValidatedFormula) :-
    validation_mode(Mode),
    
    % Check 1: Sequent syntax confusion (ALWAYS check, even in propositional logic)
    check_sequent_syntax_confusion(Formula, SyntaxWarnings),
    
    % Check 2: Biconditional misuse (only in FOL context)
    detect_fol_context(Formula, IsFOL),
    (   IsFOL ->
        check_bicond_misuse(Formula, BicondWarnings)
    ;   BicondWarnings = []
    ),
    
    % Combine warnings
    append(SyntaxWarnings, BicondWarnings, AllWarnings),
    
    % Handle combined warnings
    handle_warnings(AllWarnings, Mode, ValidatedFormula, Formula).

% Handle warnings according to mode
handle_warnings([], _, Formula, Formula) :- !.
handle_warnings(_Warnings, silent, Formula, Formula) :- !.
handle_warnings(Warnings, permissive, Formula, Formula) :-
    report_warnings(Warnings),
    prompt_continue.
handle_warnings(Warnings, strict, _, _) :-
    report_warnings(Warnings),
    write('? Validation failed in strict mode. Formula rejected.'), nl,
    fail.

% Prompt user to continue
prompt_continue :-
    write('Continue despite warnings? (y/n): '),
    read(Response),
    (   Response = y -> true
    ;   Response = yes -> true
    ;   write('? Proof attempt cancelled.'), nl, fail
    ).
% =========================================================================
% FOL CONTEXT DETECTION
% =========================================================================
% A formula is in FOL context if it contains:
%   - Quantifiers (?, ?)
%   - Predicate applications p(t1,...,tn) with n > 0
%   - Equality between terms
%   - Function symbols (including Skolem functions)

detect_fol_context(Formula, true) :-
    (   contains_quantifier(Formula)
    ;   contains_predicate_application(Formula)
    ;   contains_equality(Formula)
    ;   contains_function_symbol(Formula)
    ), !.
detect_fol_context(_, false).

% Logical connective identification
is_logical_connective(_ => _).
is_logical_connective(_ & _).
is_logical_connective(_ | _).
is_logical_connective(_ <=> _).
is_logical_connective(~ _).
is_logical_connective(#).
is_logical_connective(![_-_]:_).
is_logical_connective(?[_-_]:_).

% =========================================================================
% BICONDITIONAL MISUSE DETECTION
% =========================================================================
% Detects <=> used between terms instead of formulas
% Example: (a <=> b) should likely be (a = b) in FOL

check_bicond_misuse(Formula, Warnings) :-
    findall(Warning, detect_bicond_in_terms(Formula, Warning), Warnings).

% =========================================================================
% BICONDITIONAL MISUSE DETECTION (IMPROVED)
% =========================================================================
% Only warn if <=> appears in a TERM CONTEXT (not formula context)

detect_bicond_in_terms(A <=> B, warning(bicond_between_terms, A, B)) :-
    % Both sides are clearly terms (constants or function applications)
    is_definitely_term(A),
    is_definitely_term(B),
    !.

detect_bicond_in_terms(Term, Warning) :-
    compound(Term),
    Term \= (_ <=> _),  % Don't recurse into biconditionals we already checked
    Term =.. [_|Args],
    member(Arg, Args),
    detect_bicond_in_terms(Arg, Warning).

% =========================================================================
% DEFINITELY A TERM (not a formula)
% =========================================================================
% Conservative: only flag obvious cases

is_definitely_term(X) :- 
    var(X), !.  % Variable (term)

is_definitely_term(X) :- 
    atomic(X),
    \+ known_predicate(X),  % Constant, not predicate
    !.

is_definitely_term(f_sk(_,_)) :- !.  % Skolem function

is_definitely_term(Term) :-
    compound(Term),
    \+ is_logical_connective(Term),
    Term =.. [F|Args],
    Args \= [],
    % Must be a KNOWN function symbol (not predicate)
    is_known_function(F),
    !.

% =========================================================================
% KNOWN FUNCTION REGISTRY
% =========================================================================
% Users can register function symbols to improve detection

:- dynamic known_function/1.

% Default common function symbols
known_function(succ).   % Successor
known_function(plus).
known_function(times).
known_function(father).  % father(x) is a term
known_function(mother).

register_function(F) :-
    \+ known_function(F),
    assertz(known_function(F)).

is_known_function(F) :-
    known_function(F), !.

% Heuristic fallback: if NOT a known predicate, assume function
% (This is conservative - avoid false positives)
is_known_function(F) :-
    \+ known_predicate(F),
    \+ member(F, [f, g, h, i, j, k, p, q, r, s]),  % Ambiguous symbols
    !.

% =========================================================================
% SEQUENT SYNTAX CONFUSION DETECTION
% =========================================================================
% Detects common mistakes:
%   [P] => [Q]  (WRONG - looks like sequent but uses =>)
%   P > Q       (WRONG - looks like implication but uses >)

check_sequent_syntax_confusion(Formula, Warnings) :-
    findall(Warning, detect_sequent_confusion(Formula, Warning), Warnings).

% Case 1: [List] => [List] - user probably meant sequent syntax
detect_sequent_confusion([_|_] => [_|_], warning(list_implication, 'Use > for sequents, not =>')) :- !.
detect_sequent_confusion([_|_] => _, warning(list_implication_left, 'Left side is a list - use > for sequents')) :- !.
detect_sequent_confusion(_ => [_|_], warning(list_implication_right, 'Right side is a list - use > for sequents')) :- !.

% Case 2: Atom > Atom - user probably meant implication
detect_sequent_confusion(A > B, warning(atom_turnstile, 'Use => for implication, not >')) :-
    atomic(A),
    atomic(B),
    !.

% Case 3: Complex formula > Complex formula - likely implication
detect_sequent_confusion(A > B, warning(formula_turnstile, 'Use => for implication between formulas, not >')) :-
    is_formula(A),
    is_formula(B),
    !.

% Recursive search
detect_sequent_confusion(Term, Warning) :-
    compound(Term),
    Term \= (_ => _),  % Don't recurse into implications
    Term \= (_ > _),   % Don't recurse into turnstiles
    Term =.. [_|Args],
    member(Arg, Args),
    detect_sequent_confusion(Arg, Warning).

% Helper: check if something is a formula (not a list or term)
is_formula(Term) :-
    compound(Term),
    (   is_logical_connective(Term)
    ;   Term =.. [F|Args], Args \= [], known_predicate(F)
    ).

% Term identification (not a formula)
% A term is: constant, variable, or function application
is_term_not_formula(X) :- 
    atomic(X), !.  % Constant or variable
is_term_not_formula(f_sk(_,_)) :- !.  % Skolem function
is_term_not_formula(Term) :-
    compound(Term),
    \+ is_logical_connective(Term),
    Term =.. [F|Args],
    Args \= [],
    \+ known_predicate(F),  % Function, not predicate
    !.

% =========================================================================
% WARNING REPORTS
% =========================================================================

report_warnings([]) :- !.
report_warnings(Warnings) :-
    length(Warnings, N),
    nl,
    format('?  ~d WARNING(S) DETECTED:~n', [N]),
    nl,
    maplist(print_warning, Warnings),
    nl,
    write('? TIPS:'), nl,
    write('   o Theorems:  prove(p => q).        % implication'), nl,
    write('   o Sequents:  prove([p] > [q]).     % turnstile ?'), nl,
    write('   o FOL:       use = for equality, <=> for biconditional'), nl,
    nl.

print_warning(warning(bicond_between_terms, A, B)) :-
    format('   ?  (~w <=> ~w): biconditional between terms detected.~n', [A, B]),
    format('      -> Did you mean (~w = ~w)?~n', [A, B]).

% NEW: Sequent syntax warnings
print_warning(warning(list_implication, Msg)) :-
    format('   ?  Syntax error: ~w~n', [Msg]),
    write('      Example: prove([p, q] > [p & q]).  % CORRECT'), nl,
    write('               prove([p, q] => [p & q]). % WRONG'), nl.

print_warning(warning(list_implication_left, Msg)) :-
    format('   ?  Syntax error: ~w~n', [Msg]),
    write('      -> Use [Premises] > [Conclusion] for sequents'), nl.

print_warning(warning(list_implication_right, Msg)) :-
    format('   ?  Syntax error: ~w~n', [Msg]),
    write('      -> Use [Premises] > [Conclusion] for sequents'), nl.

print_warning(warning(atom_turnstile, Msg)) :-
    format('   ?  Syntax error: ~w~n', [Msg]),
    write('      Example: prove(p => q).       % CORRECT (implication)'), nl,
    write('               prove(p > q).        % WRONG'), nl,
    write('               prove([p] > [q]).    % CORRECT (sequent)'), nl.

print_warning(warning(formula_turnstile, Msg)) :-
    format('   ?  Syntax error: ~w~n', [Msg]),
    write('      -> Use => for implications, > only for sequents'), nl,
    write('      -> Sequent syntax: [Premises] > [Conclusions]'), nl.

% =========================================================================
% UTILITY: AUTO-SUGGESTION (optional feature)
% =========================================================================
% Suggests automatic correction of <=> to = in term contexts

suggest_auto_correction(Formula, CorrectedFormula) :-
    replace_bicond_with_eq(Formula, CorrectedFormula).

replace_bicond_with_eq(A <=> B, A1 = B1) :-
    is_term_not_formula(A),
    is_term_not_formula(B),
    !,
    replace_bicond_with_eq(A, A1),
    replace_bicond_with_eq(B, B1).
replace_bicond_with_eq(Term, Result) :-
    compound(Term),
    Term =.. [F|Args],
    maplist(replace_bicond_with_eq, Args, NewArgs),
    Result =.. [F|NewArgs], !.
replace_bicond_with_eq(Term, Term).

% =========================================================================
% EXAMPLES FOR TESTING
% =========================================================================
/*
% Test cases:

% Should warn (term <=> term):
?- validate_and_warn(((a <=> b) & f(a)) => f(b), V).

% Should NOT warn (formula <=> formula):
?- validate_and_warn((p <=> q) => (p => q), V).

% Should warn in FOL context:
?- validate_and_warn(![x]:((x <=> a) => p(x)), V).

% Should NOT warn in propositional context:
?- validate_and_warn((a <=> b) => (b <=> a), V).  % if a,b are prop vars

*/
% =========================================================================
% END OF MODULE
% =========================================================================
% =========================================================================
% tests_pelletier.pl (mise a jour : Pel_18 corrigee en formule valide)
% Suite silencieuse Pelletier + benchmarks avec safe_time_out fallback.
% =========================================================================
/*
:- module(tests_pelletier,
    [ run_pelletier/0,
      run_pelletier_named/1,
      pelletier_tests/1,
      set_pelletier_timeout/1,
      pelletier_timeout/1,
      known_invalid/1
    ]).

:- use_module(library(lists)).
*/
% -------------------------------------------------------------------------
% Timeout configurable (en secondes). Valeur par defaut : 10 secondes.
% -------------------------------------------------------------------------
:- dynamic pelletier_timeout/1.
pelletier_timeout(10).

set_pelletier_timeout(Secs) :-
    ( number(Secs), Secs > 0 ->
        retractall(pelletier_timeout(_)),
        assertz(pelletier_timeout(Secs))
    ;
        throw(error(domain_error(positive_number, Secs), set_pelletier_timeout/1))
    ).

% -------------------------------------------------------------------------
% safe_time_out/3: wrapper robuste pour executer Goal avec timeout.
% - If time_out/3 exists, uses it.
% - Else if call_with_time_limit/2 exists, uses it.
% - Else runs goal without timeout.
% Result: success | failed | time_out | error(E)
% -------------------------------------------------------------------------
safe_time_out(Goal, Secs, Result) :-
    ( current_predicate(time_out/3) ->
        catch(time_out(Goal, Secs, R), E, (Result = error(E), !)),
        !,
        map_time_out_result(R, Result)
    ; current_predicate(call_with_time_limit/2) ->
        catch((call_with_time_limit(Secs, Goal), Result = success),
              time_limit_exceeded,
              ( Result = time_out )),
        !
    ;
        catch(( (call(Goal) -> Result = success ; Result = failed) ),
              E,
              ( Result = error(E) ))
    ).

map_time_out_result(time_out, time_out) :- !.
map_time_out_result(success, success) :- !.
map_time_out_result(failed, failed) :- !.
map_time_out_result(R, success) :- R \= time_out, R \= failed, R \= success, !.

% -------------------------------------------------------------------------
% Liste des tests (Name - Formula)
% Respecte la syntaxe du driver : predicats p,q,... ; constantes a,b,c,... ; vars v,w,x,y,z
% Quantificateurs: ![x]: et ?[x]: (sans espace)
% -------------------------------------------------------------------------
:- multifile pelletier_tests/1.
pelletier_tests([
    'Pel_01_drinker' - (?[x]:(p(x) => ![y]:(p(y)))),
    'Pel_02_dn_forall_exists' - ((~(![x]:p(x))) <=> (?[x]:(~p(x)))),
    'Pel_03_forall_inst' - ((![x]:p(x)) => p(a)),
    'Pel_04_forall_preserve_exist' - ((![x]:(p(x) => q(x))) => ((?[x]:p(x)) => ?[x]:q(x))),
    'Pel_05_exists_conj_split' - ((?[x]:(p(x) & q(x))) => (?[x]:p(x) & ?[x]:q(x))),
    'Pel_06_leibniz' - (((a = b) & p(a)) => p(b)),
    'Pel_07_eq_sym' - ((a = b) <=> (b = a)),
    'Pel_08_eq_trans' - (((a = b) & (b = c)) => (a = c)),
    'Pel_09_quantifier_swap_failure' - ((![x]:(?[y]:r(x,y))) => ?[y]:(![x]:r(x,y))),
    'Pel_10_exist_forall_exchange' - ((?[y]:(![x]:p(x,y))) => (![x]:(?[y]:p(x,y)))),
    'Pel_11_existential_elim_schema' - ((?[x]:p(x)) => ((![x]:(p(x) => q)) => q)),
    'Pel_12_univ_distrib_impl' - ((![x]:(p(x) => q)) <=> ((?[x]:p(x)) => q)),
    'Pel_13_contraposition_classical' - ((p => q) <=> (~q => ~p)),
    'Pel_14_material_implication' - (((~ p | q) <=> (p => q))),
    'Pel_15_hypothetical_syllogism' - (((p => q) & (q => r)) => (p => r)),
    'Pel_16_existential_preservation' - (((![x]:(p(x) => q(x))) & ?[x]:p(x)) => ?[x]:q(x)),
    'Pel_17_biimp_to_impls' - ((p <=> q) => ((p => q) & (q => p))),
    % Pel_18 corrected: ?x (P(x) ? Q(x)) ? (?x P(x)) ? (?x Q(x))  (valid)
    'Pel_18_classical_choice' - ((?[x]:(p(x) | q(x))) <=> (?[x]:p(x) | ?[x]:q(x))),
    'Pel_19_pelletier_sample1' - ((![x]:(p(x) => ?[y]:q(x,y))) => ?[y]:(![x]:(p(x) => q(x,y)))),
    'Extra_01_drinker_variant' - (?[x]:(p(x) => ![y]:(p(y) | q(y)))),
    'Extra_03_choice_like' - ((![x]:(p(x) => q(x)) & ?[x]:p(x)) => ?[x]:q(x)),
    'Extra_04_equality_leibniz_pred' - (((a = b) & r(a)) => r(b)),
    'Extra_05_mixed_quant' - ((?[x]:(![y]:r(x,y))) => (![y]:(?[x]:r(x,y)))),
    'Extra_06_double_negation' - ((~ ~ p) => p),
    'Extra_07_peirce_variant' - ((((p => q) => p) => p)),
    'Extra_08_explosion' - ((p & ~ p) => #),
    'Extra_09_transfer' - ((![x]:(p(x) & q(x))) => (![x]:p(x) & ![x]:q(x)))
]).

% -------------------------------------------------------------------------
% known_invalid/1: tests intentionally skipped (none for Pel_18 anymore)
% -------------------------------------------------------------------------
:- dynamic known_invalid/1.
% Example: known_invalid('Pel_XX').

% -------------------------------------------------------------------------
% Runner: run_pelletier/0
% -------------------------------------------------------------------------
run_pelletier :-
    pelletier_tests(Tests),
    writeln('=== PELLETIER / HARD FOL TEST SUITE (silent, timeout enabled) ==='),
    run_pelletier_list(Tests, 1, 0, 0, 0, Tot),
    Tot = [Total, Proven, Failed, Skipped],
    nl,
    format('Done: ~d tests. Proven: ~d. Failed: ~d. Skipped: ~d.~n', [Total, Proven, Failed, Skipped]),
    writeln('===============================================================').

run_pelletier_list([], _, Proved, Failed, Skipped, [Total,Proved,Failed,Skipped]) :-
    Total is Proved + Failed + Skipped.
run_pelletier_list([Name-Formula|Rest], N, PAcc, FAcc, SAcc, Tot) :-
    format('~n[~d] ~w : ', [N, Name]),
    ( known_invalid(Name) ->
        writeln('SKIPPED (INVALID)'),
        PAcc1 is PAcc, FAcc1 is FAcc, SAcc1 is SAcc + 1
    ;
        pelletier_timeout(TOSeconds),
        catch(
            ( safe_time_out((decide(Formula) -> Status = proved ; Status = not_proved), TOSeconds, Result),
              interpret_safe_result(Result, Status, Outcome)
            ),
            E,
            Outcome = error(E)
        ),
        report_outcome(Outcome),
        ( Outcome = proved -> PAcc1 is PAcc + 1 ; PAcc1 is PAcc ),
        ( Outcome = proved -> FAcc1 is FAcc ; FAcc1 is FAcc + 1 ),
        SAcc1 is SAcc
    ),
    N1 is N + 1,
    run_pelletier_list(Rest, N1, PAcc1, FAcc1, SAcc1, Tot).

interpret_safe_result(time_out, _Status, timeout) :- !.
interpret_safe_result(success, proved, proved) :- !.
interpret_safe_result(success, not_proved, not_proved) :- !.
interpret_safe_result(failed, _Status, not_proved) :- !.
interpret_safe_result(error(E), _Status, error(E)) :- !.
interpret_safe_result(_, Status, Outcome) :- ( Status == proved -> Outcome = proved ; Outcome = not_proved ).

report_outcome(proved) :- writeln('PROVED').
report_outcome(not_proved) :- writeln('NOT PROVED').
report_outcome(timeout) :- writeln('TIMEOUT').
report_outcome(error(E)) :- format('ERROR: ~w~n', [E]).

% -------------------------------------------------------------------------
% run single named test
% -------------------------------------------------------------------------
run_pelletier_named(Name) :-
    pelletier_tests(Tests),
    ( member(Name-Formula, Tests) ->
        ( known_invalid(Name) ->
            writeln('SKIPPED (INVALID)')
        ;
            pelletier_timeout(TOSeconds),
            format('Running test ~w with timeout ~w seconds...~n', [Name, TOSeconds]),
            catch(
                ( safe_time_out((decide(Formula) -> writeln('PROVED') ; writeln('NOT PROVED')), TOSeconds, Res),
                  ( Res == time_out -> writeln('TIMEOUT') ; true )
                ),
                E, format('ERROR: ~w~n', [E])
            )
        )
    ;
        format('Test ~w not found.~n', [Name])
    ).

% =========================================================================
% END of Pelletier tests
% =========================================================================

% =================================================================
% 1. BASIC TESTS - MINIMAL PROPOSITIONAL LOGIC
% =================================================================
% Identity and implication introduction tests
test_identity_simple :-
    write('1.'), nl,
    prove(p => p).
test_identity_complex :-
    write('2.'), nl,
    prove(p => (q => p)).
test_permutation :-
    write('3.'), nl,
    prove(p => (q => (p & q))).
% Conjunction tests
test_conjunction_intro :-
    write('4.'), nl,
    prove((p & q) => (q & p)).
test_conjunction_assoc :-
    write('5.'), nl,
    prove(((p & q) & r) => (p & (q & r))).
% Disjunction tests
test_disjunction_intro :-
    write('6.'), nl,
    prove(p => (p | q)).
test_disjunction_comm :-
    write('7.'), nl,
    prove((p | q) => (q | p)).
test_disjunction_elim :-
    write('8.'), nl,
    prove(((p => r) & (q => r)) => ((p | q) => r)).
% Biconditional tests
test_distrib_disj_over_conj :-
        write('9.'),nl,
        prove(((p | q) & (p | r)) <=> (p | (q & r))).
test_biconditional_intro :-
    write('10.'), nl,
    prove((p => q) => ((q => p) => (p <=> q))).
test_biconditional_elim :-
    write('11.'), nl,
    prove((p <=> q) => (p => q)).
% Modus Tollens tests (CORRECTED)
test_modus_tollens :-
    write('12.'), nl,
    prove(((p => q) & ~ q) => ~ p).
test_modus_tollens_complex :-
    write('13.'), nl,
    prove(((p => (q => r)) & ~ r) => (p => ~ q)).
test_absurdity_chain_m :-
    write('14.'), nl,
    prove(p => (~ p => #)).
% Negation introduction/elimination tests
test_negation_intro :-
    write('15.'), nl,
    prove((p => #) => ~ p).
test_negation_elim :-
    write('16.'), nl,
    prove((p & ~ p) => #).
% =================================================================
% 2. INTUITIONISTIC TESTS - NEGATION
% =================================================================
% Contradiction tests
test_contradiction_anything :-
    write('17.'), nl,
    prove(# => p).
test_absurdity_chain_i :-
    write('18.'), nl,
    prove((~ p => #) <=> ((p => #) => p)).
test_dn_Peirce :-
    write('19.'), nl,
    prove(~  ~  (((p => q) => p) => p)).
test_dn_Dummett :-
    write('20.'), nl,
    prove(~  ~  ((p => q) | (q => p))).
test_dn_Dummett :-
    write('21.'), nl,
    prove(~  ~  ((p => q) | (q => p))).
test_dn_classical_contraposition :-
    write('22.'), nl,
    prove(~  ~  ((~  q => ~  p) <=> (p => q))).
% =================================================================
% 3. CLASSICAL TESTS - BEYOND INTUITIONISTIC LOGIC
% =================================================================
% Indirect proof tests
test_indirect_proof :-
    write('23.'), nl,
    prove( ~  ~  p => p).
test_excluded_middle :-
    write('24.'), nl,
    prove(p | ~  p).
test_material_implication :-
    write('25.'), nl,
    prove((( ~  p | q) <=> (p => q))).
% Classical contraposition tests
test_contraposition_strong :-
    write('26.'), nl,
    prove(( ~  q => ~  p) => (p => q)).
test_absurdity_chain_c :-
    write('27.'), nl,
    prove((~ p => #) => p), nl.
% =================================================================
% 4. QUANTIFIER TESTS - CORRECTED SYNTAX
% =================================================================
% Basic universal tests
test_universal_intro :-
    write('28.'), nl,
    prove(![x]:(p(x) => p(x))).
test_universal_elim :-
    write('29.'), nl,
    prove((![x]:p(x)) => p(a)).
test_universal_distribution :-
    write('30.'), nl,
    prove((![x]:(p(x) => q(x))) => ((![x]:p(x)) => (![x]:q(x)))).
% Basic existential tests
test_existential_intro :-
    write('31.'), nl,
    prove(p(a) => (?[x]:p(x))).
test_existential_elim :-
    write('32.'), nl,
    prove((?[x]:p(x)) => ((![x]:(p(x) => q)) => q)).
test_mixed_quantifiers :-
    write('33.'), nl,
    prove((?[y]:(![x]:p(x,y))) => (![x]:(?[y]:p(x,y)))).
test_quantifier_negation :-
    write('34.'), nl,
    prove((~ (![x]:p(x))) <=> (?[x]: ~  p(x))).
test_Spinoza :-
        write('35. Spinoza: "nothing is contingent" '), nl,
        prove((![x]:(~ c(x) <=> (?[y]:n(y,x) | ?[z]:d(z,x))) & ![x]:(?[z]:d(z,x))) => ![x]: ~ c(x)).
test_Lepage :-
        write( '36. Lepage, Elements de logique contemporaine, p. 202, ex. 14*-g'), nl,
        prove((![x]:(f(x) <=> g(x)) & ![x]:(h(x) <=> i(x)) & ?[x]:(i(x) & ![y]:(f(y) => j(y)))) => ?[x]:(h(x) & ![y]:(j(y) | ~ g(y)))).
test_fol_instantiation :-
    write('37.'), nl,
    prove(![x]:p(x) => ?[x]:p(x)), nl.
test_fol_quantifiers_permutation :-
    write('38.'), nl,
    prove((?[y]:(![x]:(f(x,y)))) => (![x]:(?[y]:(f(x,y))))), nl.
test_russell_paradox :-
    write('38. Russell'), nl,
    prove((?[y]:(![x]:(~ b(x,x) <=> b(x,y)))) => #), nl.
% =================================================================
% 5. PREMISE TESTS - PRACTICAL REASONING
% =================================================================
% Modus ponens with premises
test_modus_ponens :-
    write('39.'), nl,
    prove(((p => q) & p) => q).
test_hypothetical_syllogism :-
    write('40.'), nl,
    prove(((p => q) & (q => r)) => (p => r)).
test_disjunctive_syllogism :-
    write('41.'), nl,
    prove(((p | q) & ~  p ) => q).

% Complex tests with quantifiers - SIMPLIFIED
test_universal_instantiation :-
    write('42.'), nl,
    prove((![x]:(h(x) => m(x)) & h(a)) => m(a)).
test_existential_generalization :-
    write('43.'), nl,
    prove(m(a) => ?[x]:m(x)).
% =================================================================
% 6. STRESS TESTS - COMPLEX FORMULAS
% =================================================================
test_complex_formula_1 :-
    write('44.'), nl,
    prove((![x]:(p(x) => q(x))) => ((![x]:p(x)) => (![x]:q(x)))).
test_complex_formula_2 :-
    write('45.'), nl,
    prove(((p => q) & (r => s)) => ((p & r) => (q & s))).
test_Pelletier_17 :-
        write( '46. Pelletier 17' ),
        prove( ( ( p & ( q => r ) ) => s ) <=> ( ( ~ p | q | s ) & ( ~ p | ~ r | s ) ) ).
% =================================================================
% TEST RUNNERS
% =================================================================
run_all_tests :-
    write('========================================'), nl,
    write('FOL PROVER TEST SUITE START'), nl,
    write('========================================'), nl, nl,
    % Minimal propositional tests
    write('=== MINIMAL PROPOSITIONAL LOGIC ==='), nl,
    test_identity_simple, nl,
    test_identity_complex, nl,
    test_permutation, nl,
    test_conjunction_intro, nl,
    test_conjunction_assoc, nl,
    test_disjunction_intro, nl,
    test_disjunction_comm, nl,
    test_disjunction_elim, nl,
    test_distrib_disj_over_conj, nl,
    test_biconditional_intro, nl,
    test_biconditional_elim, nl,
    test_modus_tollens, nl,
    test_modus_tollens_complex, nl,
    test_absurdity_chain_m,nl,
    test_negation_intro, nl,
    test_negation_elim, nl,
    
    % Intuitionistic tests
    write('=== INTUITIONISTIC LOGIC ==='), nl,
    test_contradiction_anything, nl,
    test_absurdity_chain_i, nl,
    test_dn_Peirce, nl,
    test_dn_Dummett,nl,
    test_dn_classical_contraposition,nl,
    
 
    % Classical tests
    write('=== CLASSICAL LOGIC ==='), nl,
    test_indirect_proof, nl,
    test_excluded_middle, nl,
    test_material_implication, nl,
    test_contraposition_strong, nl,
    
    % Quantifier tests
    write('=== QUANTIFIERS ==='), nl,
    test_universal_intro, nl,
    test_universal_elim, nl,
    test_universal_distribution, nl,
    test_existential_intro, nl,
    test_existential_elim, nl,
    test_mixed_quantifiers, nl,
    test_quantifier_negation, nl,
    test_Spinoza,nl,
    test_Lepage,nl,
    test_fol_instantiation,nl,
    test_fol_quantifiers_permutation,nl,
    test_russell_paradox,nl,
    
   
    write('=== Usual logical truths ==='), nl,
    test_modus_ponens, nl,
    test_hypothetical_syllogism, nl,
    test_disjunctive_syllogism, nl,
    test_universal_instantiation, nl,
    test_existential_generalization, nl,
    
    % Stress tests
    write('=== STRESS TESTS ==='), nl,
   % test_complex_formula_1, nl,
    test_complex_formula_2, nl,
    test_Pelletier_17,nl,
    
    write('========================================'), nl,
    write('TEST SUITE END'), nl,
    write('========================================'), nl,
    !.

% Quick tests for immediate verification
quick_tests :-
    write('=== QUICK TESTS ==='), nl,
    test_identity_simple, nl,
    test_modus_tollens, nl.

% Individual MT test for debugging
test_mt_only :-
    write('=== ISOLATED MT TEST ==='), nl,
    test_modus_tollens, nl.


% =========================================================================
% TESTS FOL - FORMULES SIMPLES
% =========================================================================
   
%=================================================================
% SEQUENT TESTS - PROPOSITIONAL LOGIC ONLY
% Tests for sequents with premises (avoiding classical disjunction theorems)
% =================================================================

% =================================================================
% 1. BASIC SEQUENT TESTS - MINIMAL LOGIC
% =================================================================

% Identity with premises
test_seq_identity_premise :-
    write('47.'), nl,
    prove([p] > [p]), nl.

test_seq_weakening :-
    write('48.'), nl,
    prove([p, q] > [p]), nl.

test_seq_implication_intro :-
    write('49.'), nl,
    prove([p] > [q => p]), nl.

% =================================================================
% 2. CONJUNCTION SEQUENTS
% =================================================================

test_seq_conjunction_intro :-
    write('50.'), nl,
    prove([p, q] > [p & q]), nl.

test_seq_conjunction_elim_left :-
    write('51'), nl,
    prove([p & q] > [p]), nl.

test_seq_conjunction_elim_right :-
    write('52.'), nl,
    prove([p & q] > [q]), nl.

test_seq_conjunction_comm :-
    write('53.'), nl,
    prove([p & q] > [q & p]), nl.

test_seq_conjunction_assoc :-
    write('54.'), nl,
    prove([(p & q) & r] > [p & (q & r)]), nl.

test_seq_conjunction_nested :-
    write('55.'), nl,
    prove([p, q, r] > [(p & q) & r]), nl.

% =================================================================
% 3. IMPLICATION SEQUENTS
% =================================================================

test_seq_modus_ponens :-
    write('56.'), nl,
    prove([p => q, p] > [q]), nl.

test_seq_hypothetical_syllogism :-
    write('57.'), nl,
    prove([p => q, q => r] > [p => r]), nl.

test_seq_implication_chain :-
    write('58.'), nl,
    prove([p => q, q => r, p] > [r]), nl.

test_seq_curry :-
    write('59.'), nl,
    prove([(p & q) => r] > [p => (q => r)]), nl.

test_seq_uncurry :-
    write('60.'), nl,
    prove([p => (q => r)] > [(p & q) => r]), nl.

% =================================================================
% 4. DISJUNCTION SEQUENTS (NON-CLASSICAL)
% =================================================================

test_seq_disj_intro_left :-
    write('61.'), nl,
    prove([p] > [(p | q)]), nl.

test_seq_disj_intro_right :-
    write('62.'), nl,
    prove([q] > [(p | q)]), nl.

test_seq_disj_elim :-
    write('63.'), nl,
    prove([(p | q), p => r, q => r] > [r]), nl.

test_seq_disj_syllogism :-
    write('64.'), nl,
    prove([(p | q), ~ p] > [q]), nl.

test_seq_disj_comm :-
    write('65.'), nl,
    prove([(p | q)] > [(q | p)]), nl.

% =================================================================
% 5. NEGATION SEQUENTS - INTUITIONISTIC
% =================================================================

test_seq_negation_intro :-
    write('66.'), nl,
    prove([p => #] > [~ p]), nl.

test_seq_negation_elim :-
    write('67.'), nl,
    prove([p, ~ p] > [#]), nl.

test_seq_explosion :-
    write('68.'), nl,
    prove([#] > [p]), nl.

test_seq_modus_tollens :-
    write('69.'), nl,
    prove([p => q, ~ q] > [~ p]), nl.

test_seq_contraposition_weak :-
    write('70.'), nl,
    prove([p => q] > [~ q => ~ p]), nl.

test_seq_double_negation_intro :-
    write('71.'), nl,
    prove([p] > [~ ~ p]), nl.

% =================================================================
% 6. BICONDITIONAL SEQUENTS
% =================================================================

test_seq_biconditional_intro :-
    write('72.'), nl,
    prove([p => q, q => p] > [p <=> q]), nl.

test_seq_biconditional_elim_left :-
    write('73.'), nl,
    prove([p <=> q] > [p => q]), nl.

test_seq_biconditional_elim_right :-
    write('74.'), nl,
    prove([p <=> q] > [q => p]), nl.

test_seq_biconditional_modus_ponens :-
    write('75.'), nl,
    prove([p <=> q, p] > [q]), nl.

% =================================================================
% 7. COMPLEX SEQUENTS - INTUITIONISTIC
% =================================================================

test_seq_complex_1 :-
    write('76.'), nl,
    prove([(p => q) , (q => r), p] > [r]), nl.

test_seq_complex_2 :-
    write('77.'), nl,
    prove([p , (q | r)] > [((p & q) | (p & r))]), nl.

test_seq_complex_3 :-
    write('78.'), nl,
    prove([(p | q) , (p | r)] > [(p | (q & r))]), nl.

test_seq_complex_4 :-
    write('79.'), nl,
    prove([p => (q => r)] > [q => (p => r)]), nl.



% =================================================================
% 8. DOUBLE NEGATION SEQUENTS - INTUITIONISTIC
% =================================================================

test_seq_dn_peirce :-
    write('80.'), nl,
    prove([~ (((p => q) => p) => p)] > [#]), nl.

test_seq_dn_lem :-
    write('81.'), nl,
    prove([~ (p | ~ p)] > [#]), nl.

test_seq_dn_dummett :-
    write('82.'), nl,
    prove([~ ((p => q) | (q => p))] > [#]), nl.

% =================================================================
% TEST RUNNERS
% =================================================================

run_prop_seq :-
    write('========================================'), nl,
    write('SEQUENT TESTS - PROPOSITIONAL LOGIC'), nl,
    write('========================================'), nl, nl,
    
    write('=== 1. BASIC SEQUENTS ==='), nl,
    test_seq_identity_premise,
    test_seq_weakening,
    test_seq_implication_intro,
    
    write('=== 2. CONJUNCTION SEQUENTS ==='), nl,
    test_seq_conjunction_intro,
    test_seq_conjunction_elim_left,
    test_seq_conjunction_elim_right,
    test_seq_conjunction_comm,
    test_seq_conjunction_assoc,
    test_seq_conjunction_nested,
    
    write('=== 3. IMPLICATION SEQUENTS ==='), nl,
    test_seq_modus_ponens,
    test_seq_hypothetical_syllogism,
    test_seq_implication_chain,
    test_seq_curry,
    test_seq_uncurry,
    
    write('=== 4. DISJUNCTION SEQUENTS ==='), nl,
    test_seq_disj_intro_left,
    test_seq_disj_intro_right,
    test_seq_disj_elim,
    test_seq_disj_syllogism,
    test_seq_disj_comm,
    
    write('=== 5. NEGATION SEQUENTS ==='), nl,
    test_seq_negation_intro,
    test_seq_negation_elim,
    test_seq_explosion,
    test_seq_modus_tollens,
    test_seq_contraposition_weak,
    test_seq_double_negation_intro,
    
    write('=== 6. BICONDITIONAL SEQUENTS ==='), nl,
    test_seq_biconditional_intro,
    test_seq_biconditional_elim_left,
    test_seq_biconditional_elim_right,
    test_seq_biconditional_modus_ponens,
    
    write('=== 7. COMPLEX SEQUENTS ==='), nl,
    test_seq_complex_1,
    test_seq_complex_2,
    test_seq_complex_3,
    test_seq_complex_4,
    
    write('=== 8. DOUBLE NEGATION SEQUENTS ==='), nl,
    test_seq_dn_peirce,
    test_seq_dn_lem,
    test_seq_dn_dummett,
    
    write('========================================'), nl,
    write('SEQUENT TESTS END'), nl,
    write('========================================'), nl,
    !.

% Quick tests
quick_sequent_tests :-
    write('=== QUICK SEQUENT TESTS ==='), nl,
    test_seq_identity_premise,
    test_seq_modus_ponens,
    test_seq_disj_syllogism,
    test_seq_ltoto_2,
    write('=== QUICK TESTS END ==='), nl.
% =================================================================
% SEQUENT TESTS - FIRST ORDER LOGIC (FOL)
% Tests for sequents with quantifiers and predicates
% =================================================================

% =================================================================
% BASIC QUANTIFIER SEQUENTS
% =================================================================
test_seq_forall_elim :-
    write('83.'), nl,
    prove([![x]:p(x)] > [p(a)]).

test_seq_exists_intro :-
    write('84.'), nl,
    prove([p(a)] > [?[x]:p(x)]).

test_seq_exists_elim :-
    write('85.'), nl,
    prove([?[x]:p(x), ![x]:(p(x) => q)] > [q]).

% =================================================================
% QUANTIFIER DISTRIBUTION
% =================================================================

test_seq_forall_distribution :-
    write('86.'), nl,
    prove([![x]:(p(x) => q(x)), ![x]:p(x)] > [![x]:q(x)]).

test_seq_exists_distribution :-
    write('87.'), nl,
    prove([?[x]:(p(x) & q(x))] > [?[x]:p(x) & ?[x]:q(x)]).

test_seq_mixed_quantifiers :-
    write('88.'), nl,
    prove([?[y]:(![x]:p(x,y))] > [![x]:(?[y]:p(x,y))]).

% =================================================================
% QUANTIFIER NEGATION (DE MORGAN FOR QUANTIFIERS)
% =================================================================

test_seq_neg_forall :-
    write('89.'), nl,
    prove([~ (![x]:p(x))] <> [?[x]: ~ p(x)]).

test_seq_neg_exists :-
    write('90.'), nl,
    prove([~ (?[x]:p(x))] <> [![x]: ~ p(x)]).

% =================================================================
% MODUS PONENS WITH QUANTIFIERS
% =================================================================

test_seq_forall_mp :-
    write('91.'), nl,
    prove([![x]:(p(x) => q(x)), p(a)] > [q(a)]).

test_seq_exists_mp :-
    write('92.'), nl,
    prove([?[x]:p(x), ![x]:(p(x) => q(x))] > [?[x]:q(x)]).

% =================================================================
% CLASSICAL LOGIC WITH QUANTIFIERS
% =================================================================

test_seq_barber_paradox :-
    write('93.'), nl,
    prove([?[y]:(![x]:(~ b(x,x) <=> b(x,y)))] > [#]).

test_seq_drinker :-
    write('94.'), nl,
    prove([~ #] > [?[x]:(d(x) => ![y]:d(y))]).

% =================================================================
% SYLLOGISMS WITH QUANTIFIERS
% =================================================================

test_seq_barbara :-
    write('95.'), nl,
    prove([![x]:(m(x) => p(x)), ![x]:(s(x) => m(x))] > [![x]:(s(x) => p(x))]).

test_seq_darii :-
    write('96.'), nl,
    prove([![x]:(m(x) => p(x)), ?[x]:(s(x) & m(x))] > [?[x]:(s(x) & p(x))]).

test_seq_socrates :-
    write('97.'), nl,
    prove([![x]:(h(x) => m(x)), h(socrates)] > [m(socrates)]).

% =================================================================
% EQUALITY REASONING
% =================================================================

test_seq_eq_reflexive :-
    write('98.'), nl,
    prove([~ #] > [a = a]).

test_seq_eq_symmetric :-
    write('99.'), nl,
    prove([a = b] > [b = a]).

test_seq_eq_transitive :-
    write('100.'), nl,
    prove([a = b, b = c] > [a = c]).

test_seq_eq_substitution :-
    write('101.'), nl,
    prove([a = b, p(a)] > [p(b)]).

test_seq_eq_congruence :-
    write('102.'), nl,
    prove([a = b] > [f(a) = f(b)]).

% =================================================================
% COMPLEX FOL SEQUENTS
% =================================================================

test_seq_spinoza :-
    write('103. Spinoza'), nl,
    prove([
        ![x]:(~ c(x) <=> (?[y]:n(y,x) | ?[z]:d(z,x))),
        ![x]:(?[z]:d(z,x))
    ] > [![x]: ~ c(x)]).

test_seq_lepage :-
    write('104. Lepage'), nl,
    prove([
        ![x]:(f(x) <=> g(x)),
        ![x]:(h(x) <=> i(x)),
        ?[x]:(i(x) & ![y]:(f(y) => j(y)))
    ] > [?[x]:(h(x) & ![y]:(j(y) | ~ g(y)))]).

% =================================================================
% BICONDITIONAL SEQUENTS
% =================================================================

test_seq_bicond_left :-
    write('105.'), nl,
    prove([a <=> b, a] > [b]).

test_seq_bicond_right :-
    write('106.'), nl,
    prove([a => b, b => a] > [a <=> b]).

test_seq_bicond_quantifier :-
    write('107.'), nl,
    prove([![x]:(p(x) <=> q(x)), p(a)] > [q(a)]).

% =================================================================
% TEST RUNNERS
% =================================================================

run_fol_seq :-
        retractall(fitch_line(_, _, _, _)),      % <- Nettoyage global
    retractall(abbreviated_line(_)),
    write('========================================'), nl,
    write('FOL SEQUENT TEST SUITE START'), nl,
    write('========================================'), nl, nl,
    
    write('=== BASIC QUANTIFIERS ==='), nl,
    test_seq_exists_intro, nl,
    test_seq_exists_elim, nl,
    
    write('=== QUANTIFIER DISTRIBUTION ==='), nl,
    test_seq_forall_distribution, nl,
    test_seq_exists_distribution, nl,
    test_seq_mixed_quantifiers, nl,
    
    write('=== QUANTIFIER NEGATION ==='), nl,
    test_seq_neg_exists, nl,
    test_seq_neg_forall, nl,
    
    write('=== MODUS PONENS WITH QUANTIFIERS ==='), nl,
    test_seq_forall_mp, nl,
    test_seq_exists_mp, nl,
    
    write('=== CLASSICAL FOL ==='), nl,
    test_seq_barber_paradox, nl,
    test_seq_drinker, nl,
    
    write('=== SYLLOGISMS ==='), nl,
    test_seq_barbara, nl,
    test_seq_darii, nl,
    test_seq_socrates, nl,
    
    write('=== EQUALITY ==='), nl,
    test_seq_eq_reflexive, nl,
    test_seq_eq_symmetric, nl,
    test_seq_eq_transitive, nl,
    test_seq_eq_substitution, nl,
    test_seq_eq_congruence, nl,
    
    write('=== COMPLEX FOL ==='), nl,
    test_seq_spinoza, nl,
    test_seq_lepage, nl,
    
    write('=== BICONDITIONALS ==='), nl,
    test_seq_bicond_left, nl,
    test_seq_bicond_right, nl,
    test_seq_bicond_quantifier, nl,
    
    write('========================================'), nl,
    write('FOL SEQUENT TEST SUITE END'), nl,
    write('========================================'), nl.

run_quick_fol_sequent_tests :-
    write('=== QUICK FOL SEQUENT TESTS ==='), nl,
    test_seq_forall_elim, nl,
    test_seq_exists_intro, nl,
    test_seq_socrates, nl,
    test_seq_eq_transitive, nl,
    write('=== QUICK TESTS END ==='), nl.
