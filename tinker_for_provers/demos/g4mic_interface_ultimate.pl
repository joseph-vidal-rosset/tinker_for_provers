% =========================================================================
% G4-MIC ULTIMATE INTERFACE - WASM COMPATIBLE VERSION
% For use with tinker.html
% Uses read/1 (period IS required, but interface is still improved)
% =========================================================================

% =========================================================================
% MAIN ENTRY POINT
% =========================================================================

start :-
    write('========================================'), nl,
    write('G4-mic Interactive Mode'), nl,
    write('========================================'), nl,
    interactive_loop(prove).

% Start directly in decide mode
start_decide :-
    write('G4-mic (decide mode)'), nl,
    write('Commands: quit, help, switch'), nl, nl,
    interactive_loop(decide).

% Start with prover selection
start_choose :-
    write('Choose prover:'), nl,
    write('  1. prove'), nl,
    write('  2. decide'), nl,
    write('  3. auto'), nl,
    write('Enter choice: '),
    read(ChoiceAtom),
    (   ChoiceAtom = 1 -> interactive_loop(prove)
    ;   ChoiceAtom = 2 -> interactive_loop(decide)
    ;   ChoiceAtom = 3 -> interactive_loop(auto)
    ;   write('Invalid choice, using prove'), nl,
        interactive_loop(prove)
    ).

% =========================================================================
% MAIN LOOP
% =========================================================================

interactive_loop(Prover) :-
    show_prompt(Prover),
    read(Input),
    process_command(Input, Prover).

% Show appropriate prompt
show_prompt(prove) :- write('prove> ').
show_prompt(decide) :- write('decide> ').
show_prompt(auto) :- write('auto> ').

% Process user commands
process_command(quit, _) :- 
    !,
    write('Goodbye!'), nl.

process_command(help, Prover) :- 
    !,
    show_help, 
    interactive_loop(Prover).

process_command(examples, Prover) :- 
    !,
    show_examples, 
    interactive_loop(Prover).

process_command(switch, _) :- 
    !,
    write('Switching prover...'), nl,
    start_choose.

% Check for special command forms
process_command(prove(Formula), Prover) :-
    !,
    execute_with_prover(prove, Formula),
    interactive_loop(Prover).

process_command(decide(Formula), Prover) :-
    !,
    execute_with_prover(decide, Formula),
    interactive_loop(Prover).

process_command(tptp(Term), Prover) :-
    !,
    execute_tptp(Term),
    interactive_loop(Prover).

% Default: execute with current prover
process_command(Formula, Prover) :-
    execute_with_prover(Prover, Formula),
    interactive_loop(Prover).

% =========================================================================
% EXECUTION
% =========================================================================

% Execute formula with appropriate prover
execute_with_prover(prove, Formula) :-
    !,
    catch(prove(Formula), 
          Error, 
          (write('Error in prove: '), write(Error), nl)).

execute_with_prover(decide, Formula) :-
    !,
    catch(decide(Formula), 
          Error, 
          (write('Error in decide: '), write(Error), nl)).

execute_with_prover(auto, Formula) :-
    !,
    (   current_predicate(prove/1)
    ->  write('(using prove)'), nl,
        catch(prove(Formula), Error, 
              (write('Error: '), write(Error), nl))
    ;   current_predicate(decide/1)
    ->  write('(using decide)'), nl,
        catch(decide(Formula), Error, 
              (write('Error: '), write(Error), nl))
    ;   write('Error: Neither prove/1 nor decide/1 is available!'), nl
    ).

% Execute TPTP term
execute_tptp(fof(Name, Role, Formula)) :-
    !,
    write('TPTP: '), write(Name), write(' ('), write(Role), write(')'), nl,
    (   (Role = conjecture ; Role = theorem)
    ->  catch(prove(Formula), Error,
              (write('Error: '), write(Error), nl))
    ;   Role = axiom
    ->  write('Axiom asserted: '), write(Formula), nl
    ;   write('Unknown role: '), write(Role), nl
    ).

execute_tptp(Term) :-
    write('Not a valid TPTP fof/3 term: '), write(Term), nl.

% =========================================================================
% HELP SYSTEM
% =========================================================================

show_help :-
    write('========================================'), nl,
    write('G4-mic Help'), nl,
    write('========================================'), nl,
    write('Operators:'), nl,
    write('  ~     negation'), nl,
    write('  &     conjunction (and)'), nl,
    write('  |     disjunction (or)'), nl,
    write('  =>    conditional (implies)'), nl,
    write('  <=>   biconditional (iff)'), nl,
    write('  #     falsity (bottom)'), nl, nl,
    write('Commands:'), nl,
    write('  quit.             Exit'), nl,
    write('  help.             Show this help'), nl,
    write('  examples.         Show examples'), nl,
    write('  switch.           Change prover'), nl, nl,
    write('Usage:'), nl,
    write('  Formula.          Prove with current prover'), nl,
    write('  prove(Formula).   Force use of prove'), nl,
    write('  decide(Formula).  Force use of decide'), nl,
    write('  tptp(fof(...)).   Use TPTP format'), nl, nl,
    write('Examples:'), nl,
    write('  (p => q) => (~q => ~p).'), nl,
    write('  decide(p | ~p).'), nl,
    write('  tptp(fof(test, conjecture, p => p)).'), nl,
    write('========================================'), nl, nl.

show_examples :-
    write('========================================'), nl,
    write('Example Formulas'), nl,
    write('========================================'), nl,
    write('Classical tautologies:'), nl,
    write('  (p => q) => (~q => ~p).'), nl,
    write('  p | ~p.'), nl,
    write('  ~~p => p.'), nl, nl,
    write('Intuitionistic theorems:'), nl,
    write('  p => ~~p.'), nl,
    write('  ~(p & ~p).'), nl, nl,
    write('With decide:'), nl,
    write('  decide((p => q) => (~q => ~p)).'), nl, nl,
    write('TPTP format:'), nl,
    write('  tptp(fof(mt, conjecture, (p => q) => (~q => ~p))).'), nl,
    write('========================================'), nl, nl.

% =========================================================================
% CONVENIENCE ALIASES
% =========================================================================

% Ultra-short command
go :- start.

% For François
francois :- 
    write('Bonjour François !'), nl,
    write('Entre tes formules (avec un point à la fin) :'), nl, nl,
    start.

% =========================================================================
% QUICK OPERATORS (for non-interactive use)
% =========================================================================

:- op(1199, fx, >>).
:- op(1199, fx, ?>).
:- op(1199, fx, tptp).

% Quick prove
>> Formula :- prove(Formula).

% Quick decide  
?> Formula :- decide(Formula).

% Quick TPTP
tptp Term :- execute_tptp(Term).

% =========================================================================
% USAGE EXAMPLES
% =========================================================================
%
% In tinker.html console:
%
% ?- start.
% prove> (p => q) => (~q => ~p).
% [proof displayed]
% prove> quit.
%
% ?- start_decide.
% decide> p | ~p.
% [result displayed]
% decide> quit.
%
% ?- start_choose.
% Choose prover: 1
% prove> p => p.
% [proof displayed]
%
% Quick operators:
% ?- >> (p => q) => (~q => ~p).
% ?- ?> p | ~p.
%
% =========================================================================
