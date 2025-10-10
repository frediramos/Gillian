var p_symb = symb_string();
var obj = {};
obj[p_symb] = 1;
var v = obj["p"];
Assume("p" = p_symb);
Assert(v = 1);
