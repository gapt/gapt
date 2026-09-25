fof(f1,axiom,(
  ( ! [X0] : (p(X0)) )),
  file('Problems/martin05.p',a1)).
fof(f2,conjecture,(
  p(a)),
  file('Problems/martin05.p',c1)).
fof(f3,negated_conjecture,(
  ~p(a)),
  inference(negated_conjecture,[status(cth)],[f2])).
fof(f4,plain,(
  ~p(a)),
  inference(flattening,[status(thm)],[f3])).
fof(f5,plain,(
  ~p(a)),
  inference(cnf_transformation,[status(thm)],[f4])).
fof(f6,plain,(
  $false),
  inference(resolution,[status(thm)],[f1,f5])).
