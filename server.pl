/*  Part of SWI-Prolog

    Author:        Jan Wielemaker
    E-mail:        J.Wielemaker@vu.nl
    WWW:           http://www.swi-prolog.org
    Copyright (c)  2022-2025, SWI-Prolog Solutions b.v.
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in
       the documentation and/or other materials provided with the
       distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
    BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
    LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
*/

:- use_module(library(http/http_server)).
:- use_module(library(http/http_files)).
:- use_module(library(http/http_json)).
:- use_module(library(main)).
:- use_module(library(option)).
:- use_module(library(dcg/high_order)).
:- use_module(library(base64)).

user:file_search_path(web, '../src/wasm/demos').
user:file_search_path(web, '../src/wasm/demos/tinker').
user:file_search_path(web, 'src').
user:file_search_path(wasm_library, 'home').
user:file_search_path(scasp,  Dir) :-
    getenv('SCASP_HOME', Dir).

:- http_handler('/', http_redirect(see_other, '/wasm/'), []).
:- http_handler('/wasm/shell',  http_redirect(see_other, '/wasm/tinker'), []).
:- http_handler('/wasm/tinker', reply_html_test('tinker.html'), []).
:- http_handler('/wasm/test',   reply_html_test('test.html'), []).
:- http_handler('/wasm/cbg',    reply_html_test('cbg.html'), []).
:- http_handler('/wasm/',       index, []).
:- http_handler('/wasm/',
                http_reply_from_files(web(.), [static_gzip(true)]), [prefix]).
:- http_handler('/wasm/swipl/',
                http_reply_from_files(wasm_library(.),
                                      [static_gzip(true)]), [prefix]).

% Handler pour conversion PNG des preuves
:- http_handler('/wasm/proof_png', handle_proof_png, []).


reply_html_test(File, Request) :-
    http_reply_file(web(File),
                    [ headers([ 'Cross-Origin-Opener-Policy'('same-origin'),
                                'Cross-Origin-Embedder-Policy'('require-corp')
                              ])],
                    Request).

:- if(absolute_file_name(scasp(.), _, [file_type(directory), file_errors(fail)])).
:- http_handler('/wasm/scasp/', http_reply_from_files(scasp(.), []), [prefix]).
:- endif.


:- initialization(main, main).

opt_type(port,        port,        nonneg).
opt_type(p,           port,        nonneg).
opt_type(interactive, interactive, boolean).
opt_type(i,           interactive, boolean).

opt_help(port, "Port to listen to (default 8080)").
opt_help(interactive, "Become interactive").

server(Options) :-
    merge_options(Options, [port(8080)], Options1),
    http_server(Options1).

main(Argv) :-
    argv_options(Argv, _Pos, Options),
    server(Options),
    (   option(interactive(true), Options)
    ->  cli_enable_development_system
    ;   thread_get_message(quit)
    ).


                /*******************************
                *          DEMO INDEX          *
                *******************************/

demo(tinker,           "SWI-Tinker, a SWI-Prolog playground").
demo(cbg,              "A port of Paul Brown's Tau-Prolog application").
demo('doge/doge.html', "A port of Doge, a Tau-Prolog example").
demo('chat80.html',    "Embed the CHAT80 question answering system").
demo('bind.html',      "Illustrates binding an event, passing a \c
                        DOM object to Prolog").
demo(test,             "Demo and tests calling Prolog").
demo('engines.html',   "Demo and test for using engines").
demo('bench.html',     "Benchmark the JavaScript interface").

index(_Request) :-
    reply_html_page(
        [ title("SWI-Prolog WASM demos")
        ],
        [ h1("SWI-Prolog WASM demos"),
          p(["Demos for running SWI-Prolog compiled to WASM in your browser. \c
          See ", a(href('https://swi-prolog.discourse.group/t/swi-prolog-in-the-browser-using-wasm'), "Wiki on Discourse"), " for status and usage"]),
          ul(\foreach(demo(Link, Title), demo_li(Link, Title)))
        ]).

demo_li(Link, Title) -->
    { absolute_file_name(web(Link), _,
                         [ access(read),
                           extensions(['', html]),
                           file_errors(fail)
                         ]),
      atom_concat('/wasm/', Link, HREF)
    },
    !,
    html(li(a(href(HREF), Title))).
demo_li(_, _) -->
    [].


                /*******************************
                *      CONVERSION PNG          *
                *******************************/

%! handle_proof_png(+Request) is det.
%
%  Handler HTTP pour convertir une preuve LaTeX en image PNG.

handle_proof_png(Request) :-
    http_read_json_dict(Request, Data),
    LaTeXCode = Data.latex_code,
    Style = Data.get(style, all),
    proof_to_png(LaTeXCode, Style, Base64PNG),
    format(atom(DataURL), 'data:image/png;base64,~w', [Base64PNG]),
    reply_json_dict(_{success: true, image: DataURL}).

%! proof_to_png(+LaTeXCode, +Style, -Base64PNG) is det.
%
%  Convertit du code LaTeX en image PNG encodée en base64.
%  Support multi-pages avec combinaison verticale des images.
%  Adapte l'orientation selon le style:
%  - sequent et tree: orientation paysage (landscape) pour affichage horizontal
%  - fitch: orientation portrait pour affichage vertical
%  - all: orientation paysage par défaut

proof_to_png(LaTeXCode, Style, Base64PNG) :-
    % Déterminer la géométrie selon le style
    (   (Style = sequent ; Style = tree)
    ->  % Paysage pour sequent et tree (plus large)
        Geometry = '\\usepackage[landscape,margin=0.3cm,paperwidth=50cm,paperheight=29.7cm]{geometry}\n'
    ;   Style = fitch
    ->  % Portrait pour fitch (plus haut, moins large)
        Geometry = '\\usepackage[portrait,margin=0.3cm,paperwidth=29.7cm,paperheight=50cm]{geometry}\n'
    ;   % all ou autre: paysage par défaut
        Geometry = '\\usepackage[landscape,margin=0.3cm,paperwidth=50cm,paperheight=29.7cm]{geometry}\n'
    ),
    
    tmp_file(proof, TmpBase),
    atom_concat(TmpBase, '.tex', TexFile),
    atom_concat(TmpBase, '.pdf', PdfFile),
    atom_concat(TmpBase, '_page', PngBase),
    atom_concat(TmpBase, '_combined.png', CombinedPng),
    
    open(TexFile, write, Out),
    write(Out, '\\documentclass[12pt]{article}\n'),
    write(Out, Geometry),
    write(Out, '\\usepackage{fitch}\n'),
    write(Out, '\\usepackage{bussproofs}\n'),
    write(Out, '\\usepackage{amsmath}\n'),
    write(Out, '\\usepackage{amssymb}\n'),
    write(Out, '\\pagestyle{empty}\n'),
    write(Out, '\\begin{document}\n'),
    write(Out, LaTeXCode),
    write(Out, '\n\\end{document}\n'),
    close(Out),
    
    format(atom(Cmd1), '/usr/bin/pdflatex -interaction=nonstopmode -output-directory=/tmp ~w >/dev/null 2>&1', [TexFile]),
    shell(Cmd1),
    sleep(2),
    
    % Convertir toutes les pages du PDF en PNG séparés
    format(atom(Cmd2), '/usr/bin/pdftoppm -png -r 300 ~w ~w 2>/dev/null', [PdfFile, PngBase]),
    shell(Cmd2),
    sleep(1),
    
    % Vérifier combien de pages ont été générées et les combiner
    (   atom_concat(PngBase, '-1.png', FirstPage),
        exists_file(FirstPage)
    ->  % Multi-pages : combiner verticalement avec ImageMagick
        format(atom(Cmd3), 'convert ~w-*.png -append ~w 2>/dev/null', [PngBase, CombinedPng]),
        shell(Cmd3),
        sleep(1),
        FinalPng = CombinedPng
    ;   % Une seule page
        atom_concat(PngBase, '.png', SinglePage),
        (   exists_file(SinglePage)
        ->  FinalPng = SinglePage
        ;   FinalPng = none
        )
    ),
    
    (   FinalPng \= none,
        exists_file(FinalPng)
    ->  open(FinalPng, read, In, [type(binary)]),
        read_stream_to_codes(In, Codes),
        close(In),
        base64(Codes, Base64PNG)
    ;   Base64PNG = ''
    ),
    
    % Nettoyer tous les fichiers temporaires
    catch(delete_file(TexFile), _, true),
    catch(delete_file(PdfFile), _, true),
    catch(delete_file(CombinedPng), _, true),
    forall(
        (between(1, 20, N),
         format(atom(PngN), '~w-~w.png', [PngBase, N]),
         exists_file(PngN)),
        catch(delete_file(PngN), _, true)
    ),
    catch(delete_file(atom_concat(PngBase, '.png')), _, true),
    atom_concat(TmpBase, '.aux', Aux), catch(delete_file(Aux), _, true),
    atom_concat(TmpBase, '.log', Log), catch(delete_file(Log), _, true).
