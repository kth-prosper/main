

fun add_to_simplist thm = simp_thms_list := (thm::(!simp_thms_list));


val trivial_true = store_thm("trivial_true", ``T``, FULL_SIMP_TAC (srw_ss()) []);


fun update_mode_changing_comp_list opr = mode_changing_comp_list := (opr::(! mode_changing_comp_list));
 

fun save_comb_thm (name, th, listelement) =
            let val () = update_mode_changing_comp_list listelement
            in
                save_thm(name, th)
            end;


fun get_trans_thm uf =
    if (uf = ``priv_mode_constraints``) then
       trans_priv_mode_constraints_thm
    else if (uf = ``strict_unt``) then
       trans_strict_unt_thm
    else
       trans_empty_unt_thm;
         

fun get_reflex_thm uf =
    if (uf = ``priv_mode_constraints``) then
       reflex_priv_mode_constraints_thm
    else if (uf = ``strict_unt``) then
       reflex_strict_unt_thm
    else
      reflex_empty_unt_thm;

fun get_sim_reflex_thm uy =
    if (uy = ``priv_mode_similar``) then
       reflex_priv_mode_similar_thm
    else
      reflex_empty_sim_thm;


fun get_unt_def uf =
    if (uf = ``priv_mode_constraints``) then
       priv_mode_constraints_def
    else if (uf = ``strict_unt``) then
       strict_unt_def
    else
      empty_unt_def;


fun get_sim_def uy =
    if (uy = ``priv_mode_similar``) then
       priv_mode_similar_def
    else if (uy = ``empty_similar_def``) then
      empty_sim_def
    else
       CONJ fixed_flags_def (CONJ fix_flags_def (CONJ empty_sim_def priv_mode_similar_def)) ;


fun prove_it a src_inv trg_inv uf uy =
     let val () = global_mode := ``16w:bool[5]`` 
     in
       prove  a src_inv trg_inv  ([uf, uy, ``27w:word5``, ``_thm``])  ([(get_trans_thm uf), (get_reflex_thm uf), (get_unt_def uf), (get_sim_def uy), trivial_true, (get_sim_reflex_thm uy)])
     end;


fun obtain_proofs () =
  case top_goals() of 
     x::rl => 
          let val (_, to_show) = x
          in
            case (dest_term to_show) of
                COMB (rcstu, simp)
                => case dest_term rcstu of
                     COMB (rcst, unt)
                     => case dest_term rcst of 
                            COMB (rcs, i2)
                            => case (dest_term rcs) of 
                                   COMB (rc, i1) => 
                                        case (dest_term rc) of
                                             COMB (rel, comp)  =>  let val (thm, _ ) = prove_it comp i1 i2 unt simp in
                                                                   thm
                                                                   end
                                             | _ => (trivial_true)
                               | _ => (trivial_true)
                        | _ => (trivial_true)
                   | _ => (trivial_true)
              | _ => (trivial_true)
          end
     | _ => (trivial_true);



fun GO_ON_TAC () =
    let val thm = obtain_proofs ()
    in
        ASSUME_TAC thm THEN FULL_SIMP_TAC (srw_ss()) []
    end;


fun go_on cnt = case cnt of
                        0 => e(GO_ON_TAC())
                       |1 => e(GO_ON_TAC())
                       |_ => let val _= e(GO_ON_TAC()) in go_on (cnt-1) end; 

fun go_on_p cnt = go_on cnt;


fun thm_prove a =
	    let val (cplx_thm, _) = (prove_it a ``assert_mode 16w`` ``assert_mode 16w`` ``empty_unt`` ``empty_sim``)
	    in
	       cplx_thm
	    end;

fun thm_proveP a =
	    let val (cplx_thm, _) = (prove_it a ``assert_mode 16w`` ``comb_mode 16w 27w`` ``priv_mode_constraints`` ``priv_mode_similar``)
	    in
	       cplx_thm
	    end;


fun thm_proveS a =
	    let val (cplx_thm, _) = (prove_it a ``assert_mode 16w`` ``assert_mode 16w`` ``strict_unt`` ``empty_sim``)
	    in
	       cplx_thm
	    end;


fun prove_and_save (a, name) =
            let val th = thm_prove a
            in
               save_thm(name, th)
            end;


fun prove_and_save_e (a, name) =
            let val th = thm_prove a
            in
               save_thm(name, (MATCH_MP extras_lem2 th))
            end;

fun prove_and_save_s (a, name) =
            let val th = thm_proveS a
            in
               save_thm(name, (MATCH_MP extras_lem4 th))
            end;

fun prove_and_save_p (a, name, lelement) =
            let val th = thm_proveP a
            in
               save_comb_thm(name, th, lelement)
            end;

fun prove_and_save_p_helper (a, name) =
            let val th = thm_proveP a
            in
               save_thm(name, th)
            end;




