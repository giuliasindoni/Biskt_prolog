


refute( Formulae, _ ) :-
        write( 'refute: ' ), write(Formulae), nl,
        %write( '        ' ), write(Rules), nl,
        fail. 

refute( Formulae, [tf_close] ) :-
   select( S:(Phi=t), Formulae, Rest ),
   member( S:(Phi=f),  Rest ), !,
   applying( tf_close ).

refute( Formulae, [false_is_t_close] ) :-
      member( _:(false=t), Formulae ), !,
      applying(false_is_t_close ).

%% True conjunction
refute( Formulae, [t_con | Rules] ) :-
        select( S:(and(Phi,Psi)=t), Formulae, Rest ), !,
        applying( t_con ),
        refute( [S:(Phi=t), S:(Psi=t) | Rest], Rules ).

%% False disjunction
refute( Formulae, [f_dis | Rules] ) :-
        select( S:(or(Phi,Psi)=f), Formulae, Rest ), !,
        applying(f_dis),
        refute( [S:(Phi=f), S:(Psi=f) | Rest], Rules ).

%% True disjunction
refute( Formulae, [t_dis, Rules1, Rules2 ] ) :-
        select( S:(or(Phi,Psi)=t), Formulae, Rest ), !,
        applying(t_dis),
        refute( [S:(Phi=t) | Rest], Rules1 ), 
        refute( [S:(Psi=t) | Rest], Rules2 ).

%% False conjunction
refute( Formulae, [f_con, Rules1, Rules2] ) :-
        select( S:(and(Phi,Psi)=f), Formulae, Rest ),
        !,
        applying(f_con),
        refute( [S:(Phi=f) | Rest], Rules1 ), 
        refute( [S:(Psi=f) | Rest], Rules2 ).

%% True node first negation
refute( Formulae, [t_nneg | Rules] ) :-
        select( S:(nneg(Phi)=t), Formulae, Rest ),
        !,
        applying(t_nneg),
        member( h(S,T), Rest ),
        refute( [T:(Phi=f) | Rest], Rules ).
%% True node first negation --- special case with T=S
refute( Formulae, [t_nneg_s | Rules] ) :-
        select( S:(nneg(Phi)=t), Formulae, Rest ),
        applying(t_nneg_s),
        refute( [S:(Phi=f) | Rest], Rules ).


%% False edge first negation
refute( Formulae, [f_eneg | Rules] ) :-
        select( S:(eneg(Phi)=f), Formulae, Rest ),
        member( h(T,S), Rest ),
        !,
        applying(f_eneg),
        refute( [T:(Phi=t) | Rest], Rules ).
%% False edge first negation --- special case with T=S
refute( Formulae, [f_eneg_s | Rules] ) :-
        select( S:(eneg(Phi)=f), Formulae, Rest ),
        !,
        applying(f_ineg_s),
        refute( [S:(Phi=t) | Rest], Rules ).


%% False node first negation
refute( Formulae, [f_nneg | Rules] ) :-
        select( S:(nneg(Phi)=f), Formulae, Rest ),
        !,
        T = @(nneg(Phi),S),
        refute( [h(S,T), T:(Phi=t) | Rest], Rules ). 

%% True edge first negation
refute( Formulae, [t_eneg | Rules] ) :-
        select( S:(eneg(Phi)=t), Formulae, Rest ),
        !,
        T = @(eneg(Phi),S),
        refute( [h(T,S), T:(Phi=f) | Rest], Rules ). 

%% Frame rule for h relation

%% Monotonicity of truth wrt h
refute( Formulae, [h_mon | Rules] ) :-
      member( S:(Phi=t), Formulae ),
      member( h(S,T), Formulae ),
      \+( member(T:(Phi=t), Formulae) ), %% Check not already present
      !,
      applying( h_mon ),
      refute( [ T:(Phi=t) | Formulae ], Rules ).

%% Transitivity of h
refute( Formulae, [h_trans | Rules] ) :-
      member( h(S,T), Formulae ),
      member( h(T,U), Formulae ),
      \+( member( h(S,U), Formulae) ), %% Check not already present
      applying( h_trans ), !,
      refute( [h(S,U) | Formulae], Rules ).

refute( Formulae, _ ) :- !,
      write( '!! CANNOT REFUTE !!' ), nl,
      write( '!! No rule applicable to the current formula set:'), nl,
      write( '      '), write( Formulae), nl, nl,
      fail.

applying( Rule ):- write('Applying: '), write(Rule), nl.


example( 1, 
         [s:( and( eneg(nneg(x)), y ) =t ), h(w,s), h(w,m)],  
          m:( and( x, eneg(nneg(y)) ) =t )
       ).

prove( EgN ) :-
       example( EgN, Premisses, Conclusion ),
       Conclusion = S:(Phi=t),
       refute( [ S:(Phi=f) | Premisses ] ).


run :- prove( 1 ), !,
       format( "** Proved example ~p (refutation tableau closed).").
run :- format( "!! Could not prove example ~p").

:- run.


















