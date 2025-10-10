var v_symb = symb_number();
var p_symb = symb_string();
var obj = { p: v_symb };
Assume(p_symb = "p");
var v = obj[p_symb];
Assert(v_symb = v);