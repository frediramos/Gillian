var x = symb_string();
var y = symb_string();
var z = symb_string();

var obj = {};
obj[x] = 1;
obj[y] = 2;
obj[z] = 3;

Assume((z = x) or (z = y));

var ret = obj[z];