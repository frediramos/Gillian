var obj = { p1: 1, p2: 2 }
delete obj.p1;
var v1 = obj["p1"];
var v2 = obj["p2"];
Assert(v1 = undefined);
Assert(v2 = 2);