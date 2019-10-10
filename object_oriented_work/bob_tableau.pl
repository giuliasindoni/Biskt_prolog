%% META-LEVEl RULES 

%% Objects are property value lists:
% e.g [prop1 = this, prop2 = [some, items]] ) 
% or
% [available = [.., ..], used = [...., ... ], relations = ???]

ob_prop_val( Object, Prop, Val ) :-
     member( Prop = Val, Object ).

%% The following rule lets us go from an old object to a new object

set_ob_prop_val( Object, Prop, Val, NewObject ) :-
     select( Prop = _, Object, Rest ),
     NewObject = [Prop=Val | Rest].

%% IN-BETWEEN RULES

%% The following rule specifies when a logic formula is in available-list

has_available_formula( State, Formula ) :-
          ob_prop_val( State, available, Formulae ),
          member( Formula, Formulae ).

%% The following rule specifies when a logic formula is in used-list

has_used_formula(State, Formula) :-
                 ob_prop_val(State, used, Formulae),
                 member(Formula, Formulae).

%% The following rule specifies when a relational formula is in relation-list

has_relational_formula(State, Rel_formula) :-
               ob_prop_val(State, relations, Rel_formulae),
               member(Rel_formula, Rel_formulae). 

%% The following rule is used to analyse a formula


consume_formula( State, Formula, NewState ):-
           ob_prop_val( State, available, FA ),
           ob_prop_val( State, used, FU ),
           select( Formula, FA, Rest ),
           set_ob_prop_val( State, available, Rest, NewState1 ),
          set_ob_prop_val( NewState1, used, [Formula | FU], NewState ).


/* 
add_formula_to_available( State, Formula, NewState ) :-
            ob_prop_val( State, available, FA ),
            set_ob_prop_val( State, available, [Formula | FA], NewState ).


*/



add_formula_to_available( State, Formula, NewState ) :-
            ob_prop_val( State, available, Available ),
            ( member(Formula, Available) ->  
              NewState = State
              ;   
              set_ob_prop_val( State, available, [Formula | Available], NewState )
            ), !.

add_formula_if_new(State, Formula, NewState ) :-
            ob_prop_val( State, used, Used ),
            ( member(Formula, Used) ->  
              NewState = State
              ;   
              add_formula_to_available( State, Formula, NewState )
            ), !.




add_rel_formula_to_relations(State, Rel_formula, NewState) :-
                             ob_prop_val(State, relations, Rel_formulae),
                             set_ob_prop_val(State, relations, [Rel_formula | Rel_formulae], NewState). 



%% -----------------RULES FOR CONTRADICTION ---------------------


refute( State, [contradiction] ):-
        has_available_formula( State, S:(Phi=t)),
        has_available_formula( State, S:(Phi=f)),
        applying(contradiction).


refute(State, [false_is_true]) :-
       has_available_formula(State, _S: (false = t)),
       applying(false_is_true).

%% -----------------NON-BRANCHING RULES and NON-CREATING ----------------------

%% Conjuction true 
%% Use add_formula_if_new to block the application of the rule if both 
%% the conclusions are in available formula or in used formula  

refute( State, [t_con | Rules] ):-
     consume_formula( State, S:(and(Phi,Psi)=t), NewState1 ),
      add_formula_if_new( NewState1, S:(Phi=t), NewState2 ),
      add_formula_if_new( NewState2, S:(Psi=t), Newstate3 ),
      !,
      applying(t_con),
      print(newstate(Newstate3)),
      refute( Newstate3, Rules ).

%% Disjunction false
%% Use add_formula_if_new to block the application of the rule if both 
%% the conclusions are in available formula or in used formula 

refute(State, [f_disj | Rules]) :-
      consume_formula(State, S: (or(Phi, Psi) = f), NewState1),
      add_formula_if_new(NewState1, S:(Phi = f), NewState2),
      add_formula_if_new(NewState2, S:(Psi = f), Newstate3),
      !,
      applying(f_disj),
      print(newstate(Newstate3)),
      refute(Newstate3, Rules). 

%% N-Negation true, Non-destructive rule

refute(State, [t_nneg | Rules]) :-
      has_available_formula(State, S:(nneg(Phi) = t )),
      has_relational_formula(State, h(S, T)),
      add_formula_if_new(State, T:(Phi = f), NewState1),
      \+(State = NewState1),
      !,
      applying(t_nneg),
      print(newstate(NewState1)),
      refute(NewState1, Rules). 


%% E-Negation false, Non-destructive rule

refute(State, [f_eneg | Rules]) :-
      has_available_formula(State, S:(eneg(Phi) = f )),
      has_relational_formula(State, h(T, S)),
      add_formula_if_new(State, T:(Phi = t), NewState1),
      \+(State = NewState1),
      !,
      applying(f_eneg),
      print(newstate(NewState1)),
      refute(NewState1, Rules).

%% White Box true

refute(State, [t_wbox | Rules]) :-
      has_available_formula(State, S:(wbox(Phi) = t)),
      has_relational_formula(State, r(S, T)),
      add_formula_if_new(State, T:(Phi = t), NewState1),
      \+(State = NewState1),
      !,
      applying(t_wbox),
      print(newstate(NewState1)),
      refute(NewState1, Rules).
 

 %% Black Diamond false

refute(State, [f_bdia | Rules]) :-
      has_available_formula(State, S:(bdia(Phi) = f)),
      has_relational_formula(State, r(T, S)),
      add_formula_if_new(State, T:(Phi = f), NewState1),
        \+(State = NewState1),
      !,
      applying(f_bdia),
      print(newstate(NewState1)),
      refute(NewState1, Rules).

%% Universal Box true

refute(State, [t_ubox | Rules]) :-
      has_available_formula(State, _S:(ubox(Phi) = t)),
      has_available_formula( State, T: (_)),
      add_formula_if_new(State, T:(Phi = t), NewState1),
      \+(State = NewState1),
      !,
      applying(t_ubox),
      print(newstate(NewState1)),
      refute(NewState1, Rules).



%% Universal Diamond false

refute(State, [f_udia | Rules]) :-
      has_available_formula(State, _S:(udia(Phi) = f)),
      has_available_formula( State, T: (_)),
      add_formula_if_new(State, T:(Phi = f), NewState1),
      \+(State = NewState1),
      !,
      applying(f_udia),
      print(newstate(NewState1)),
      refute(NewState1, Rules).





%% ---------------------- BRANCHING-RULES ------------------------------





applying( Rule ):- write('Applying: '), write(Rule), nl.    


%% ------------------------------ TESTS ------------------------------

test_object( [available = [i:(and(p,p1)=t), i:(p=t), i:(p1=f)], used=[d,e]] ).

test_object2( [available = [i: (and(p1, p2) = t)], used=[], relations = [h(i,i), h(i, j)] ] ).

test_object3( [available = [i: (nneg(p1) = t)], used=[], relations = [h(i,i), h(i, j)] ] ).

test_object4( [available = [i: (eneg(p1) = f)], used=[], relations = [h(i,i), h(j, i)] ] ).

test_object5( [available = [i: (wbox(p1) = t), i:(bdia(p2) = f)], used=[], relations = [r(i, j), r(i,i)] ] ).

test_object6( [available = [i: (bdia(p1) = f), i:(wbox(p1) = t )], used=[], relations = [r(i,i)] ] ).

test_object7( [available = [i: (ubox(p1) = t),  j:(udia(p1) = f )], used=[] ] ).

test_object8( [available = [i: (ubox( and(p1, p2) ) = t)], used=[], relations = [] ] ).

test_object9( [available = [i: (udia( or(p1, p2) ) = f)], used=[], relations = [] ] ).















