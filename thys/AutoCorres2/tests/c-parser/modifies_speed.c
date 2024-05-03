int global1;
int global2;
int global3;
int global4;
int global5;
int global6;
int global7;
int global8;
int global9;
int global10;
int
foo1 (int x) {

  global1 = x;
  global2 = x;
  global3 = x;
  global4 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;

  return x;
}
int
foo2 (int x) {

  global2 = x;
  global3 = x;
  global4 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;

  return x;
}
int
foo3 (int x) {

  global2 = x;
  global3 = x;
  global4 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;

  return x;
}
int
foo4 (int x) {

  global1 = x;
  global3 = x;
  global4 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;

  return x;
}
int
foo5 (int x) {

  global1 = x;
  global3 = x;
  global4 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;

  return x;
}
int
foo6 (int x) {

  global3 = x;
  global4 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo3 (x);

  return x;
}
int
foo7 (int x) {

  global3 = x;
  global4 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;

  return x;
}
int
foo8 (int x) {

  global1 = x;
  global2 = x;
  global4 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo4 (x);

  return x;
}
int
foo9 (int x) {

  global1 = x;
  global2 = x;
  global4 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo3 (x);

  return x;
}
int
foo10 (int x) {

  global2 = x;
  global4 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo5 (x);

  return x;
}
int
foo11 (int x) {

  global2 = x;
  global4 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;

  return x;
}
int
foo12 (int x) {

  global1 = x;
  global4 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo3 (x);
  foo4 (x);
  foo6 (x);

  return x;
}
int
foo13 (int x) {

  global1 = x;
  global4 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;

  return x;
}
int
foo14 (int x) {

  global4 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo7 (x);

  return x;
}
int
foo15 (int x) {

  global4 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo3 (x);
  foo5 (x);

  return x;
}
int
foo16 (int x) {

  global1 = x;
  global2 = x;
  global3 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo4 (x);
  foo8 (x);

  return x;
}
int
foo17 (int x) {

  global1 = x;
  global2 = x;
  global3 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;

  return x;
}
int
foo18 (int x) {

  global2 = x;
  global3 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo3 (x);
  foo6 (x);
  foo9 (x);

  return x;
}
int
foo19 (int x) {

  global2 = x;
  global3 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;

  return x;
}
int
foo20 (int x) {

  global1 = x;
  global3 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo4 (x);
  foo5 (x);
  foo10 (x);

  return x;
}
int
foo21 (int x) {

  global1 = x;
  global3 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo3 (x);
  foo7 (x);

  return x;
}
int
foo22 (int x) {

  global3 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo11 (x);

  return x;
}
int
foo23 (int x) {

  global3 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;

  return x;
}
int
foo24 (int x) {

  global1 = x;
  global2 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo3 (x);
  foo4 (x);
  foo6 (x);
  foo8 (x);
  foo12 (x);

  return x;
}
int
foo25 (int x) {

  global1 = x;
  global2 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo5 (x);

  return x;
}
int
foo26 (int x) {

  global2 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo13 (x);

  return x;
}
int
foo27 (int x) {

  global2 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo3 (x);
  foo9 (x);

  return x;
}
int
foo28 (int x) {

  global1 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo4 (x);
  foo7 (x);
  foo14 (x);

  return x;
}
int
foo29 (int x) {

  global1 = x;
  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;

  return x;
}
int
foo30 (int x) {

  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo3 (x);
  foo5 (x);
  foo6 (x);
  foo10 (x);
  foo15 (x);

  return x;
}
int
foo31 (int x) {

  global5 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;

  return x;
}
int
foo32 (int x) {

  global1 = x;
  global2 = x;
  global3 = x;
  global4 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo4 (x);
  foo8 (x);
  foo16 (x);

  return x;
}
int
foo33 (int x) {

  global1 = x;
  global2 = x;
  global3 = x;
  global4 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo3 (x);
  foo11 (x);

  return x;
}
int
foo34 (int x) {

  global2 = x;
  global3 = x;
  global4 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo17 (x);

  return x;
}
int
foo35 (int x) {

  global2 = x;
  global3 = x;
  global4 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo5 (x);
  foo7 (x);

  return x;
}
int
foo36 (int x) {

  global1 = x;
  global3 = x;
  global4 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo3 (x);
  foo4 (x);
  foo6 (x);
  foo9 (x);
  foo12 (x);
  foo18 (x);

  return x;
}
int
foo37 (int x) {

  global1 = x;
  global3 = x;
  global4 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;

  return x;
}
int
foo38 (int x) {

  global3 = x;
  global4 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo19 (x);

  return x;
}
int
foo39 (int x) {

  global3 = x;
  global4 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo3 (x);
  foo13 (x);

  return x;
}
int
foo40 (int x) {

  global1 = x;
  global2 = x;
  global4 = x;
  global6 = x;
  global7 = x;
  global8 = x;
  global9 = x;
  global10 = x;
  foo4 (x);
  foo5 (x);
  foo8 (x);
  foo10 (x);
  foo20 (x);

  return x;
}
