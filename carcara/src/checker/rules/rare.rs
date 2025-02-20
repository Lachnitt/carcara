use super::{
    assert_clause_len, assert_eq, assert_num_args,
    CheckerError, RuleArgs, RuleResult,
};
use crate::{checker::rules::*};

//TODO:This doesn't check the type of the parameters, does it need to?
//this does not check special cases for lists
// Define Rules

pub fn check_if_true(top:Rc<Term>) -> RuleResult {
    if !top.is_bool_true() {
	return Err(CheckerError::ExpectedBoolConstant(
            true,
            top.clone(),
     ));}
    Ok(())
}

pub fn check_if_false(bot:Rc<Term>) -> RuleResult {
    if !bot.is_bool_false() {
	return Err(CheckerError::ExpectedBoolConstant(
            false,
            bot.clone(),
     ));}
    Ok(())
}

//(define-rule bool-double-not-elim ((t Bool)) (not (not t)) t)
pub fn bool_double_not_elim(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 2)?;
    let t_args = &args[1];
    
    //check match
    let t_match = match_term_err!((not (not t)) = rmatch)?;

    //check target
    let t_target = rtarget;

    //check equality match = target
    assert_eq(t_match,t_target)?;

    //check equality for arguments
    assert_eq(t_match,t_args)?;

    Ok(())
}

//(define-rule bool-eq-true ((t Bool)) (= t true) t)
pub fn bool_eq_true(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 2)?;
    let t_args = &args[1];
    
    //check match
    let (t_match,top) = match_term_err!((= t_match top) = rmatch)?;
    check_if_true(top.clone())?;

    //check target
    let t_target = rtarget;

    //check equality match = target
    assert_eq(t_match,t_target)?;

    //check equality for arguments
    assert_eq(t_match,t_args)?;

    Ok(())
}

//(define-rule bool-eq-false ((t bool)) (= t false) (not t))
pub fn bool_eq_false(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 2)?;
    let t_args = &args[1];
    
    //check match
    let (t_match,bot) = match_term_err!((= t_match bot) = rmatch)?;
    check_if_false(bot.clone())?;

    //check target
    let t_target = match_term_err!((not t_target) = rtarget)?;

    //check equality match = target
    assert_eq(t_match,t_target)?;

    //check equality for arguments
    assert_eq(t_match,t_args)?;

    Ok(())
}

//(define-rule bool-eq-nrefl ((x Bool)) (= x (not x)) false)
pub fn bool_eq_nrefl(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 2)?;
    let t_args = &args[1];
    
    //check match
    let (t_match,t_match2) = match_term_err!((= t_match (not t_match2)) = rmatch)?;
    assert_eq(t_match,t_match2)?;

    //check target
    let t_target = rtarget;
    check_if_false(t_target.clone())?;

    //check equality match = target

    //check equality for arguments
    assert_eq(t_match,t_args)?;

    Ok(())
}

//(define-rule bool-impl-false1 ((t Bool)) (=> t false) (not t))
pub fn bool_impl_false1(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 2)?;
    let t_args = &args[1];
    
    //check match
    let (t_match,bot) = match_term_err!((=> t_match bot) = rmatch)?;

    if !bot.is_bool_false() {
	return Err(CheckerError::ExpectedBoolConstant(
            false,
            bot.clone(),
     ));}

    //check target
    let t_target = match_term_err!((not t_target) = rtarget)?;
    check_if_true(t_target.clone())?;

    //check equality match = target
    assert_eq(t_match,t_target)?;

    //check equality for arguments
    assert_eq(t_match,t_args)?;

    Ok(())
}

//(define-rule bool-impl-false2 ((t Bool)) (=> false t) true)
pub fn bool_impl_false2(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 2)?;
    let t_args = &args[1];
    
    //check match
    let (t_match,bot) = match_term_err!((=> bot t_match) = rmatch)?;
    check_if_false(bot.clone())?;

    //check target
    let t_target = rtarget;
    check_if_true(t_target.clone())?;

    //check equality match = target

    //check equality for arguments
    assert_eq(t_match,t_args)?;

    Ok(())
}

//(define-rule bool-impl-true1 ((t Bool)) (=> t true) true)
pub fn bool_impl_true1(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 2)?;
    let t_args = &args[1];
    
    //check match
    let (t_match,top) = match_term_err!((=> t_match top) = rmatch)?;
    check_if_true(top.clone())?;

    //check target
    let t_target = rtarget;
    check_if_true(t_target.clone())?;

    //check equality match = target

    //check equality for arguments
    assert_eq(t_match,t_args)?;

    Ok(())
}

//(define-rule bool-impl-true2 ((t Bool)) (=> true t) t)
pub fn bool_impl_true2(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 2)?;
    let t_args = &args[1];
    
    //check match
    let (top,t_match) = match_term_err!((=> top t_match) = rmatch)?;
    check_if_true(top.clone())?;

    //check target
    let t_target = rtarget;

    //check equality match = target
    assert_eq(t_match,t_target)?;

    //check equality for arguments
    assert_eq(t_match,t_args)?;

    Ok(())
}

//(define-rule bool-impl-elim ((t Bool) (s Bool)) (=> t s) (or (not t) s))
pub fn bool_impl_elim(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 3)?;
    let t_args = &args[1];
    let s_args = &args[2];
    
    //check match
    let (t_match,s_match) = match_term_err!((=> t_match s_match) = rmatch)?;

    //check target
    let (t_target,s_target) = match_term_err!((or (not t_target) s_target) = rtarget)?;

    //check equality match = target
    assert_eq(t_match,t_target)?;
    assert_eq(s_match,s_target)?;

    //check equality for arguments
    assert_eq(t_match,t_args)?;
    assert_eq(s_match,s_args)?;

    Ok(())
}

//(define-rule bool-or-true ((xs Bool :list) (ys Bool :list)) (or xs true ys) true)
pub fn bool_or_true(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 3)?;
    let xs_args = &args[1];
    let xs_contents = match_term_err!((RareList ...) = xs_args)?;
    let ys_args = &args[2];
    let ys_contents = match_term_err!((RareList ...) = ys_args)?;

    let mut pool = PrimitivePool::new(); //TODO: this is definitely not the right way
    let zs_contents = [xs_contents,&[pool.bool_true()],ys_contents].concat().clone();    
    
    //check match
    let match_contents = match_term_err!((and ...) = rmatch)?;
    assert_operation_len(Operator::Or, match_contents, xs_contents.len() + ys_contents.len() + 1)?;
    for (z, m) in zs_contents.clone().iter().zip(match_contents) {
       assert_eq(z, m)?;
    }

    //check target
    let top = rtarget;
    check_if_true(top.clone())?;

    //check equality match = target

    //check equality for arguments

    Ok(())
}

//(define-rule* bool-or-false ((xs Bool :list) (ys Bool :list)) (or xs false ys) (or xs ys))
/*pub fn bool_or_false(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {


    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 3)?;
    let xs_args = &args[1];
    let xs_contents = match_term_err!((RareList ...) = xs_args)?;
    let ys_args = &args[2];
    let ys_contents = match_term_err!((RareList ...) = ys_args)?;

    let mut pool = PrimitivePool::new(); //TODO: this is definitely not the right way
    let zs_contents = [xs_contents,&[pool.bool_false()],ys_contents].concat().clone();    
    let as_contents = [xs_contents,ys_contents].concat().clone();    
    
    //check match
    let match_contents = match_term_err!((and ...) = rmatch)?;
    assert_operation_len(Operator::Or, match_contents, zs_contents.len())?;
    for (z, m) in zs_contents.clone().iter().zip(match_contents) {
       assert_eq(z, m)?;
    }

    //check target
    let target_contents = match_term_err!((or ...) = rtarget)?;
    assert_operation_len(Operator::Or, target_contents, as_contents.len())?;
    for (a, t) in as_contents.clone().iter().zip(target_contents) {
       assert_eq(a, t)?;
    }

    //check equality match = target

    //check equality for arguments

    Ok(())
}

//(define-rule* bool-or-flatten ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list)) (or xs (or b ys) zs) (or xs b ys zs))
pub fn bool_or_flatten(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 3)?;
    let xs_args = &args[1];
    let xs_contents = match_term_err!((RareList ...) = xs_args)?;
    let b_args = &args[2];
    let ys_args = &args[3];
    let ys_contents = match_term_err!((RareList ...) = ys_args)?;
    let zs_args = &args[4];
    let zs_contents = match_term_err!((RareList ...) = zs_args)?;

    let as_contents = [&[b_args.clone()],ys_contents].concat().clone();    
    let cs_contents = [xs_contents,&[b_args.clone()],ys_contents,zs_contents].concat().clone();    
    
    //check match
    let match_contents = match_term_err!((and ...) = rmatch)?;
    let xs_length = xs_contents.len();
    assert_operation_len(Operator::Or, match_contents, xs_length + zs_contents.len() + 1)?;
    for i in 0..xs_length {
       assert_eq(&xs_contents[i],&match_contents[i])?;
    }
    let match2_contents = match_term_err!((or ...) = &match_contents[xs_length])?;
    for i in 0..as_contents.len() {
       assert_eq(&as_contents[i],&match2_contents[i])?;
    }
    for i in xs_length+1..match_contents.len() {
       assert_eq(&zs_contents[i],&match_contents[i])?;
    }

    //check target
    let target_contents = match_term_err!((or ...) = rtarget)?;
    assert_operation_len(Operator::Or, target_contents, cs_contents.len())?;
    for (c, t) in cs_contents.clone().iter().zip(target_contents) {
       assert_eq(c, t)?;
    }

    //check equality match = target

    //check equality for arguments

    Ok(())
}
*/


//(define-rule bool-and-false ((xs Bool :list) (ys Bool :list)) (and xs false ys) false)
pub fn bool_and_false(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 3)?;
    let xs_args = &args[1];//(rare-list (not (= y$n1s8 y$v_k_Table)) (not (= y$n255s8 y$v_k_Table)))invalid
    let xs_contents = match_term_err!((RareList ...) = xs_args)?;
    let ys_args = &args[2];
    let ys_contents = match_term_err!((RareList ...) = ys_args)?;

    let mut pool = PrimitivePool::new(); //TODO: this is definitely not the right way
    let zs_contents = [xs_contents,&[pool.bool_false()],ys_contents].concat().clone();    
    
    //check match
    let match_contents = match_term_err!((and ...) = rmatch)?;
    assert_operation_len(Operator::Or, match_contents, xs_contents.len() + ys_contents.len() + 1)?;
    for (z, m) in zs_contents.clone().iter().zip(match_contents) {
       assert_eq(z, m)?;
    }

    //check target
    let bot = rtarget;

    if !bot.is_bool_false() {
	return Err(CheckerError::ExpectedBoolConstant(
            false,
            bot.clone(),
     ));}

    //check equality match = target

    //check equality for arguments

    Ok(())
}

//(define-rule bool-xor-refl ((x Bool)) (xor x x) false)
pub fn bool_xor_refl(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 2)?;
    let t_args = &args[1];
    
    //check match
    let (t_match,t_match2) = match_term_err!((xor t_match t_match2) = rmatch)?;
    assert_eq(t_match,t_match2)?;

    //check target
    let bot = rtarget;
    check_if_false(bot.clone())?;

    //check equality match = target

    //check equality for arguments
    assert_eq(t_match,t_args)?;

    Ok(())
}


//(define-rule bool-xor-nrefl ((x Bool)) (xor x (not x)) true)
pub fn bool_xor_nrefl(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 2)?;
    let x_args = &args[1];
    
    //check match
    let (x_match,x_match2) = match_term_err!((xor x_match (not x_match2)) = rmatch)?;
    assert_eq(x_match,x_match2)?;

    //check target
    let x_target = rtarget;
    check_if_true(x_target.clone())?;

    //check equality match = target

    //check equality for arguments
    assert_eq(x_match,x_args)?;

    Ok(())
}

//(define-rule bool-xor-false ((x Bool)) (xor x false) x)
pub fn bool_xor_false(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 2)?;
    let x_args = &args[1];
    
    //check match
    let (x_match,bot) = match_term_err!((xor x_match bot) = rmatch)?;
    check_if_false(bot.clone())?;

    //check target
    let x_target = rtarget;

    //check equality match = target
    assert_eq(x_match,x_target)?;

    //check equality for arguments
    assert_eq(x_match,x_args)?;

    Ok(())
}

//(define-rule bool-xor-true ((x Bool)) (xor x true) (not x))
pub fn bool_xor_true(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 2)?;
    let x_args = &args[1];
    
    //check match
    let (x_match,top) = match_term_err!((xor x_match top) = rmatch)?;
    check_if_true(top.clone())?;

    //check target
    let x_target = match_term_err!((not x_target) = rtarget)?;

    //check equality match = target
    assert_eq(x_match,x_target)?;

    //check equality for arguments
    assert_eq(x_match,x_args)?;

    Ok(())
}

//(define-rule bool-xor-comm ((x Bool) (y Bool)) (xor x y) (xor y x))
pub fn bool_xor_comm(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 3)?;
    let x_args = &args[1];
    let y_args = &args[2];
    
    //check match
    let (x_match,y_match) = match_term_err!((xor x_match y_match) = rmatch)?;

    //check target
    let (y_target,x_target) = match_term_err!((xor y_target x_target) = rtarget)?;

    //check equality match = target
    assert_eq(x_match,x_target)?;
    assert_eq(y_match,y_target)?;

    //check equality for arguments
    assert_eq(x_match,x_args)?;
    assert_eq(y_match,y_args)?;

    Ok(())
}

//(define-rule bool-xor-elim ((x Bool) (y Bool)) (xor x y) (= (not x) y))
pub fn bool_xor_elim(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 3)?;
    let x_args = &args[1];
    let y_args = &args[2];
    
    //check match
    let (x_match,y_match) = match_term_err!((xor x_match y_match) = rmatch)?;

    //check target
    let (x_target,y_target) = match_term_err!((= (not x_target) y_target) = rtarget)?;

    //check equality match = target
    assert_eq(x_match,x_target)?;
    assert_eq(y_match,y_target)?;

    //check equality for arguments
    assert_eq(x_match,x_args)?;
    assert_eq(y_match,y_args)?;

    Ok(())
}

//(define-rule bool-not-eq-elim1 ((x Bool) (y Bool)) (not (= x y)) (= (not x) y))
pub fn bool_not_eq_elim1(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 3)?;
    let x_args = &args[1];
    let y_args = &args[2];
    
    //check match
    let (x_match,y_match) = match_term_err!((not (= x_match y_match)) = rmatch)?;

    //check target
    let (x_target,y_target) = match_term_err!((= (not x_target) y_target) = rtarget)?;

    //check equality match = target
    assert_eq(x_match,x_target)?;
    assert_eq(y_match,y_target)?;

    //check equality for arguments
    assert_eq(x_match,x_args)?;
    assert_eq(y_match,y_args)?;

    Ok(())
}

//(define-rule bool-not-eq-elim2 ((x Bool) (y Bool)) (not (= x y)) (= x (not y)))
pub fn bool_not_eq_elim2(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 3)?;
    let x_args = &args[1];
    let y_args = &args[2];
    
    //check match
    let (x_match,y_match) = match_term_err!((not (= x_match y_match)) = rmatch)?;

    //check target
    let (x_target,y_target) = match_term_err!((= x_target (not y_target)) = rtarget)?;

    //check equality match = target
    assert_eq(x_match,x_target)?;
    assert_eq(y_match,y_target)?;

    //check equality for arguments
    assert_eq(x_match,x_args)?;
    assert_eq(y_match,y_args)?;

    Ok(())
}

//(define-rule ite-then-true ((c Bool) (x Bool)) (ite c true x) (or c x))
pub fn ite_then_true(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 3)?;
    let c_args = &args[1];
    let x_args = &args[2];
    
    //check match
    let (c_match,top,x_match) = match_term_err!((ite c_match top x_match) = rmatch)?;
    check_if_true(top.clone())?;

    //check target
    let (c_target,x_target) = match_term_err!((or c_target x_target) = rtarget)?;

    //check equality match = target
    assert_eq(c_match,c_target)?;
    assert_eq(x_match,x_target)?;

    //check equality for arguments
    assert_eq(c_match,c_args)?;
    assert_eq(x_match,x_args)?;

    Ok(())
}

//(define-rule ite-else-false ((c Bool) (x Bool)) (ite c x false) (and c x))
pub fn ite_else_false(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 3)?;
    let c_args = &args[1];
    let x_args = &args[2];
    
    //check match
    let (c_match,x_match,bot) = match_term_err!((ite c_match x_match bot) = rmatch)?;
    check_if_false(bot.clone())?;

    //check target
    let (c_target,x_target) = match_term_err!((or c_target x_target) = rtarget)?;

    //check equality match = target
    assert_eq(c_match,c_target)?;
    assert_eq(x_match,x_target)?;

    //check equality for arguments
    assert_eq(c_match,c_args)?;
    assert_eq(x_match,x_args)?;

    Ok(())
}


//(define-rule ite-then-false ((c Bool) (x Bool)) (ite c false x) (and (not c) x))
pub fn ite_then_false(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 3)?;
    let c_args = &args[1];
    let x_args = &args[2];
    
    //check match
    let (c_match,bot,x_match) = match_term_err!((ite c_match bot x_match) = rmatch)?;
    check_if_false(bot.clone())?;

    //check target
    let (c_target,x_target) = match_term_err!((and (not c_target) x_target) = rtarget)?;

    //check equality match = target
    assert_eq(c_match,c_target)?;
    assert_eq(x_match,x_target)?;

    //check equality for arguments
    assert_eq(c_match,c_args)?;
    assert_eq(x_match,x_args)?;

    Ok(())
}


//(define-rule ite-else-true ((c Bool) (x Bool)) (ite c x true) (or (not c) x))
pub fn ite_else_true(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 3)?;
    let c_args = &args[1];
    let x_args = &args[2];
    
    //check match
    let (c_match,x_match,top) = match_term_err!((ite c_match x_match top) = rmatch)?;
    check_if_false(top.clone())?;

    //check target
    let (c_target,x_target) = match_term_err!((or (not c_target) x_target) = rtarget)?;

    //check equality match = target
    assert_eq(c_match,c_target)?;
    assert_eq(x_match,x_target)?;

    //check equality for arguments
    assert_eq(c_match,c_args)?;
    assert_eq(x_match,x_args)?;

    Ok(())
}

//(define-rule ite-then-lookahead-self ((c Bool) (x Bool)) (ite c c x) (ite c true x))
pub fn ite_then_lookahead_self(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 3)?;
    let c_args = &args[1];
    let x_args = &args[2];
    
    //check match
    let (c_match,c2_match,x_match) = match_term_err!((ite c_match c_match x_match) = rmatch)?;
    assert_eq(c_match,c2_match)?;

    //check target
    let (c_target,top,x_target) = match_term_err!((ite c_target top x_target) = rtarget)?;
    check_if_true(top.clone())?;

    //check equality match = target
    assert_eq(c_match,c_target)?;
    assert_eq(x_match,x_target)?;

    //check equality for arguments
    assert_eq(c_match,c_args)?;
    assert_eq(x_match,x_args)?;

    Ok(())
}

//(define-rule ite-else-lookahead-self ((c Bool) (x Bool)) (ite c x c) (ite c x false))
pub fn ite_else_lookahead_self(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 3)?;
    let c_args = &args[1];
    let x_args = &args[2];
    
    //check match
    let (c_match,x_match,c2_match) = match_term_err!((ite c_match x_match c2_match) = rmatch)?;
    assert_eq(c_match,c2_match)?;

    //check target
    let (c_target,x_target,bot) = match_term_err!((ite c_target x_target bot) = rtarget)?;
    check_if_false(bot.clone())?;

    //check equality match = target
    assert_eq(c_match,c_target)?;
    assert_eq(x_match,x_target)?;

    //check equality for arguments
    assert_eq(c_match,c_args)?;
    assert_eq(x_match,x_args)?;

    Ok(())
}


//(define-rule ite-then-lookahead-not-self ((c Bool) (x Bool)) (ite c (not c) x) (ite c false x))
pub fn ite_then_lookahead_not_self(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 3)?;
    let c_args = &args[1];
    let x_args = &args[2];
    
    //check match
    let (c_match,c2_match,x_match) = match_term_err!((ite c_match (not c2_match) x_match) = rmatch)?;
    assert_eq(c_match,c2_match)?;

    //check target
    let (c_target,bot,x_target) = match_term_err!((ite c_target bot x_target) = rtarget)?;
    check_if_false(bot.clone())?;

    //check equality match = target
    assert_eq(c_match,c_target)?;
    assert_eq(x_match,x_target)?;

    //check equality for arguments
    assert_eq(c_match,c_args)?;
    assert_eq(x_match,x_args)?;

    Ok(())
}

//(define-rule ite-else-lookahead-not-self ((c Bool) (x Bool)) (ite c x (not c)) (ite c x true))
pub fn ite_else_lookahead_not_self(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 3)?;
    let c_args = &args[1];
    let x_args = &args[2];
    
    //check match
    let (c_match,c2_match,x_match) = match_term_err!((ite c_match x_match (not c2_match)) = rmatch)?;
    assert_eq(c_match,c2_match)?;

    //check target
    let (c_target,x_target,top) = match_term_err!((ite c_target x_target top) = rtarget)?;
    check_if_true(top.clone())?;

    //check equality match = target
    assert_eq(c_match,c_target)?;
    assert_eq(x_match,x_target)?;

    //check equality for arguments
    assert_eq(c_match,c_args)?;
    assert_eq(x_match,x_args)?;

    Ok(())
}

//(define-rule ite-expand ((c Bool) (x Bool) (y Bool)) (ite c x y) (and (or (not c) x) (or c y)))
pub fn ite_expand(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 4)?;
    let c_args = &args[1];
    let x_args = &args[2];
    let y_args = &args[3];
    
    //check match
    let (c_match,x_match,y_match) = match_term_err!((ite c_match x_match y_match) = rmatch)?;

    //check target
    let (temp1,temp2) = match_term_err!((and temp1 temp2) = rtarget)?;
    let (c_target,x_target) = match_term_err!((or (not c_target) x_target) = temp1)?;
    let (c2_target,y_target) = match_term_err!((or c2_target y_target) = temp2)?;
    assert_eq(c_target,c2_target)?;

    //check equality match = target
    assert_eq(c_match,c_target)?;
    assert_eq(x_match,x_target)?;
    assert_eq(y_match,y_target)?;

    //check equality for arguments
    assert_eq(c_match,c_args)?;
    assert_eq(x_match,x_args)?;
    assert_eq(y_match,y_args)?;

    Ok(())
}

//(define-rule bool-not-ite-elim ((c Bool) (x Bool) (y Bool)) (not (ite c x y)) (ite c (not x) (not y)))
pub fn bool_not_ite_elim(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 4)?;
    let c_args = &args[1];
    let x_args = &args[2];
    let y_args = &args[3];
    
    //check match
    let (c_match,x_match,y_match) = match_term_err!((not (ite c_match x_match y_match)) = rmatch)?;

    //check target
    let (c_target,x_target,y_target) = match_term_err!((ite c_target (not x_target) (not y_target)) = rtarget)?;

    //check equality match = target
    assert_eq(c_match,c_target)?;
    assert_eq(x_match,x_target)?;
    assert_eq(y_match,y_target)?;

    //check equality for arguments
    assert_eq(c_match,c_args)?;
    assert_eq(x_match,x_args)?;
    assert_eq(y_match,y_args)?;

    Ok(())
}

//(define-rule ite-true-cond ((x ?) (y ?)) (ite true x y) x)
pub fn ite_true_cond(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 3)?;
    let x_args = &args[1];
    let y_args = &args[2];
    
    //check match
    let (top,x_match,y_match) = match_term_err!((ite top x_match y_match) = rmatch)?;
    check_if_true(top.clone())?;

    //check target
    let x_target = rtarget;

    //check equality match = target
    assert_eq(x_match,x_target)?;

    //check equality for arguments
    assert_eq(x_match,x_args)?;
    assert_eq(y_match,y_args)?;

    Ok(())
}


//(define-rule ite-false-cond ((x ?) (y ?)) (ite false x y) y)
pub fn ite_false_cond(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 3)?;
    let x_args = &args[1];
    let y_args = &args[2];
    
    //check match
    let (bot,x_match,y_match) = match_term_err!((ite bot x_match y_match) = rmatch)?;
    check_if_false(bot.clone())?;

    //check target
    let y_target = rtarget;

    //check equality match = target
    assert_eq(y_match,y_target)?;

    //check equality for arguments
    assert_eq(x_match,x_args)?;
    assert_eq(y_match,y_args)?;

    Ok(())
}


//(define-rule ite-not-cond ((c Bool) (x ?) (y ?)) (ite (not c) x y) (ite c y x))
pub fn ite_not_cond(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 4)?;
    let c_args = &args[1];
    let x_args = &args[2];
    let y_args = &args[3];
    
    //check match
    let (c_match,x_match,y_match) = match_term_err!((ite (not c_match) x_match y_match) = rmatch)?;

    //check target
    let (c_target,y_target,x_target) = match_term_err!((ite c_target y_target x_target) = rtarget)?;

    //check equality match = target
    assert_eq(c_match,c_target)?;
    assert_eq(x_match,x_target)?;
    assert_eq(y_match,y_target)?;

    //check equality for arguments
    assert_eq(c_match,c_args)?;
    assert_eq(x_match,x_args)?;
    assert_eq(y_match,y_args)?;

    Ok(())
}


//(define-rule ite-eq-branch ((c Bool) (x ?)) (ite c x x) x)
pub fn ite_eq_branch(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 3)?;
    let c_args = &args[1];
    let x_args = &args[2];
    
    //check match
    let (c_match,x_match,x2_match) = match_term_err!((ite c_match x_match x2_match) = rmatch)?;
    assert_eq(x_match,x2_match)?;

    //check target
    let x_target = rtarget;

    //check equality match = target
    assert_eq(x_match,x_target)?;

    //check equality for arguments
    assert_eq(c_match,c_args)?;
    assert_eq(x_match,x_args)?;

    Ok(())
}


//(define-rule ite-then-lookahead ((c Bool) (x ?) (y ?) (z ?)) (ite c (ite c x y) z) (ite c x z))
pub fn ite_then_lookahead(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 5)?;
    let c_args = &args[1];
    let x_args = &args[2];
    let y_args = &args[3];
    let z_args = &args[4];
    
    //check match
    let (c_match,temp1,z_match) = match_term_err!((ite c_match temp1 z_match) = rmatch)?;
    let (c2_match,x_match,y_match) = match_term_err!((ite c2_match x_match y_match) = temp1)?;
    assert_eq(c_match,c2_match)?;

    //check target
    let (c_target,x_target,z_target) = match_term_err!((ite c_target x_target z_target) = rtarget)?;

    //check equality match = target
    assert_eq(c_match,c_target)?;
    assert_eq(x_match,x_target)?;
    assert_eq(z_match,z_target)?;

    //check equality for arguments
    assert_eq(c_match,c_args)?;
    assert_eq(x_match,x_args)?;
    assert_eq(y_match,y_args)?;
    assert_eq(z_match,z_args)?;

    Ok(())
}


//(define-rule ite-else-lookahead ((c Bool) (x ?) (y ?) (z ?)) (ite c x (ite c y z)) (ite c x z))
pub fn ite_else_lookahead(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 5)?;
    let c_args = &args[1];
    let x_args = &args[2];
    let y_args = &args[3];
    let z_args = &args[4];
    
    //check match
    let (c_match,x_match,temp1) = match_term_err!((ite c_match x_match temp1) = rmatch)?;
    let (c2_match,y_match,z_match) = match_term_err!((ite c2_match y_match z_match) = temp1)?;
    assert_eq(c_match,c2_match)?;

    //check target
    let (c_target,x_target,z_target) = match_term_err!((ite c_target x_target z_target) = rtarget)?;

    //check equality match = target
    assert_eq(c_match,c_target)?;
    assert_eq(x_match,x_target)?;
    assert_eq(z_match,z_target)?;

    //check equality for arguments
    assert_eq(c_match,c_args)?;
    assert_eq(x_match,x_args)?;
    assert_eq(y_match,y_args)?;
    assert_eq(z_match,z_args)?;

    Ok(())
}


//(define-rule ite-then-neg-lookahead ((c Bool) (x ?) (y ?) (z ?)) (ite c (ite (not c) x y) z) (ite c y z))
pub fn ite_then_neg_lookahead(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 5)?;
    let c_args = &args[1];
    let x_args = &args[2];
    let y_args = &args[3];
    let z_args = &args[4];
    
    //check match
    let (c_match,temp1,z_match) = match_term_err!((ite c_match temp1 z_match) = rmatch)?;
    let (c2_match,x_match,y_match) = match_term_err!((ite (not c2_match) x_match y_match) = temp1)?;
    assert_eq(c_match,c2_match)?;

    //check target
    let (c_target,y_target,z_target) = match_term_err!((ite c_target y_target z_target) = rtarget)?;

    //check equality match = target
    assert_eq(c_match,c_target)?;
    assert_eq(y_match,y_target)?;
    assert_eq(z_match,z_target)?;

    //check equality for arguments
    assert_eq(c_match,c_args)?;
    assert_eq(x_match,x_args)?;
    assert_eq(y_match,y_args)?;
    assert_eq(z_match,z_args)?;

    Ok(())
}




//(define-rule ite-else-neg-lookahead ((c Bool) (x ?) (y ?) (z ?)) (ite c x (ite (not c) y z)) (ite c x y))
pub fn ite_else_neg_lookahead(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 5)?;
    let c_args = &args[1];
    let x_args = &args[2];
    let y_args = &args[3];
    let z_args = &args[4];
    
    //check match
    let (c_match,x_match,temp1) = match_term_err!((ite c_match x_match temp1) = rmatch)?;
    let (c2_match,y_match,z_match) = match_term_err!((ite (not c2_match) y_match z_match) = temp1)?;
    assert_eq(c_match,c2_match)?;

    //check target
    let (c_target,x_target,y_target) = match_term_err!((ite c_target x_target y_target) = rtarget)?;

    //check equality match = target
    assert_eq(c_match,c_target)?;
    assert_eq(x_match,x_target)?;
    assert_eq(y_match,y_target)?;

    //check equality for arguments
    assert_eq(c_match,c_args)?;
    assert_eq(x_match,x_args)?;
    assert_eq(y_match,y_args)?;
    assert_eq(z_match,z_args)?;

    Ok(())
}

//(define-rule eq-refl ((t ?)) (= t t) true)
pub fn eq_refl(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 2)?;
    let t_args = &args[1];
    
    //check match
    let (t_match,t2_match) = match_term_err!((= t_match t2_match) = rmatch)?;
    assert_eq(t_match,t2_match)?;

    //check target
    let t_target = rtarget;
    check_if_true(t_target.clone())?;

    //check equality match = target

    //check equality for arguments
    assert_eq(t_match,t_args)?;

    Ok(())
}

//(define-rule eq-symm ((t ?) (s ?)) (= t s) (= s t))
pub fn eq_symm(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 3)?;
    let t_args = &args[1];
    let s_args = &args[2];
    
    //check match
    let (t_match,s_match) = match_term_err!((= t_match s_match) = rmatch)?;

    //check target
    let (s_target,t_target) = match_term_err!((= s_target t_target) = rtarget)?;

    //check equality match = target
    assert_eq(t_match,t_target)?;
    assert_eq(s_match,s_target)?;

    //check equality for arguments
    assert_eq(t_match,t_args)?;
    assert_eq(s_match,s_args)?;

    Ok(())
}

//(define-rule distinct-binary-elim ((t ?) (s ?)) (distinct t s) (not (= t s)))
pub fn distinct_binary_elim(RuleArgs { conclusion, args, .. }: RuleArgs) -> RuleResult {

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 3)?;
    let t_args = &args[1];
    let s_args = &args[2];
    
    //check match
    let (t_match,s_match) = match_term_err!((distinct t_match s_match) = rmatch)?;

    //check target
    let (t_target,s_target) = match_term_err!((not (= t_target s_target)) = rtarget)?;

    //check equality match = target
    assert_eq(t_match,t_target)?;
    assert_eq(s_match,s_target)?;

    //check equality for arguments
    assert_eq(t_match,t_args)?;
    assert_eq(s_match,s_args)?;

    Ok(())
}





//TODO
//(define-cond-rule bool-not-true ((t Bool)) (= t false) (not t) true)
/*pub fn bool_not_true(RuleArgs { conclusion, premises, args, .. }: RuleArgs) -> RuleResult {

    //check premises
    assert_num_premises(premises, 1)?;

    //check conclusion, split up in match and target
    assert_clause_len(conclusion, 1)?;
    let (rmatch, rtarget) = match_term_err!((= f s) = &conclusion[0])?;

    //check arguments
    assert_num_args(args, 2)?;
    let t_args = &args[1];
   
    //check premises
 
    //check match
    let t_match = match_term_err!((not (not t)) = rmatch)?;

    //check target
    let t_target = rtarget;

    //check equality match = target
    assert_eq(t_match,t_target)?;

    //check equality for arguments
    assert_eq(t_match,t_args)?;

    Ok(())
}*/

pub fn rare_error (RuleArgs {  .. }: RuleArgs) -> RuleResult {
   return Err(CheckerError::RARENotFound("")) //TODO: do this directly below, so you can add rewrite name
}

pub fn get_rule(rule_name: &str) ->Rule {
    match rule_name {
      // Boolean rewrites

      // rules without conditions or lists
      "bool-double-not-elim" => bool_double_not_elim,

      "bool-eq-true" => bool_eq_true,
      "bool-eq-false" => bool_eq_false,
      "bool-eq-nrefl" => bool_eq_nrefl,

      "bool-impl-false1" => bool_impl_false1,
      "bool-impl-false2" => bool_impl_false2,
      "bool-impl-true1" => bool_impl_true1,
      "bool-impl-true2" => bool_impl_true2,
      "bool-impl-elim" => bool_impl_elim,

      "bool-xor-refl" => bool_xor_refl,
      "bool-xor-nrefl" => bool_xor_nrefl,
      "bool-xor-false" => bool_xor_false,
      "bool-xor-true" => bool_xor_true,
      "bool-xor-comm" => bool_xor_comm,
      "bool-xor-elim" => bool_xor_elim,
      //"bool-not-xor-elim" => bool_not_xor_elim,
      
      "bool-not-eq-elim1" => bool_not_eq_elim1,
      "bool-not-eq-elim2" => bool_not_eq_elim2,
      

      "ite-then-true" => ite_then_true,
      "ite-else-false" => ite_else_false,
      "ite-then-false" => ite_then_false,
      "ite-else-true" => ite_else_true,

      "ite-then-lookahead-self" => ite_then_lookahead_self,
      "ite-else-lookahead-self" => ite_else_lookahead_self,

      "ite-then-lookahead-not-self" => ite_then_lookahead_not_self,
      "ite-else-lookahead-not-self" => ite_else_lookahead_not_self,

      "ite-expand" => ite_expand,
      "bool-not-ite-elim" => bool_not_ite_elim,

      // Conditional
      //"bool-not-true" => bool_not_true,
      //"bool-not-false" => bool_not_false,
      //"ite-neg-branch" => ite_neg_branch,

      //lists
      "bool-or-true" => bool_or_true,
      "bool-and-false" => bool_and_false,
      
      
      // builtin
      "ite-true-cond" => ite_true_cond,
      "ite-false-cond" => ite_false_cond,
      "ite-not-cond" => ite_not_cond,
      "ite-eq-branch" => ite_eq_branch,

      "ite-then-lookahead" => ite_then_lookahead,
      "ite-else-lookahead" => ite_else_lookahead,
      "ite-then-neg-lookahead" => ite_then_neg_lookahead,
      "ite-else-neg-lookahead" => ite_else_neg_lookahead,

      //uf
      "eq-refl" => eq_refl,
      "eq-symm" => eq_symm,
      "distinct-binary-elim" => distinct_binary_elim,

      _ => rare_error,
    }
}

pub fn rare_rewrite(ra: RuleArgs) -> RuleResult {
  let RuleArgs { args, .. } = ra;
  assert_num_args(args, 1..)?;
  let t =
  match args[0].as_ref() {
	 Term::Const(Constant::String(t) ) => t.clone(),
	 _ => return Err(CheckerError::TermOfWrongForm("First argument of rare_rewrite needs to be name of the rewrite",args[0].clone())),
  };
  if t == "evaluate" {
        return Ok(()); //obviously not okay but ignore evaluates for now
  }
  let rule = get_rule(&t);
  rule(ra)?;
  Ok(())
  //let rule_name = match_term_err!((Term::Const s) = &args[0])?;
}


