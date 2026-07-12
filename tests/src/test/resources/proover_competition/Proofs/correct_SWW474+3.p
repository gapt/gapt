% Refutation found. Thanks to Tanya!
% SZS status Theorem for SWW474+3
% SZS output start Proof for SWW474+3
fof(f83,axiom,(
  ! [X0] : hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(X0),bot_bo784226126e_bool))),
  file('Problems/SWW/SWW474+3.p',fact_0_empty)).
fof(f87,axiom,(
  ! [X0,X1,X2] : (hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(X1),X2)) => (hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(X0),X1)) => hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(X0),X2))))),
  file('Problems/SWW/SWW474+3.p',fact_4_cut)).
fof(f149,axiom,(
  ! [X0] : (hBOOL(hoare_1795711768gleton) => (hBOOL(wT_bodies) => (hBOOL(hAPP_com_bool(wt,X0)) => hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(bot_bo784226126e_bool),hAPP_f806699093e_bool(hAPP_H1902130436e_bool(insert1744391420_state,hAPP_c1455475371_state(hoare_Mirabelle_MGT,X0)),bot_bo784226126e_bool))))))),
  file('Problems/SWW/SWW474+3.p',fact_66_MGF)).
fof(f323,axiom,(
  ! [X0] : hAPP_f806699093e_bool(collec637225377_state,X0) = X0),
  file('Problems/SWW/SWW474+3.p',fact_240_Collect__def)).
fof(f378,axiom,(
  ! [X0] : hAPP_f806699093e_bool(collec637225377_state,hAPP_H216526335e_bool(fequal1440809015_state,X0)) = hAPP_f806699093e_bool(hAPP_H1902130436e_bool(insert1744391420_state,X0),bot_bo784226126e_bool)),
  file('Problems/SWW/SWW474+3.p',fact_295_singleton__conv2)).
fof(f380,axiom,(
  ! [X0,X1] : (hBOOL(wT_bodies) => (hAPP_p799580910on_com(body,X0) = hAPP_com_option_com(some_com,X1) => hBOOL(hAPP_com_bool(wt,X1))))),
  file('Problems/SWW/SWW474+3.p',fact_297_WT__bodiesD)).
fof(f645,axiom,(
  ! [X0] : set_Ho1741238126_state(hAPP_H1633077406_state(some_H1043067815_state,X0)) = hAPP_f806699093e_bool(hAPP_H1902130436e_bool(insert1744391420_state,X0),bot_bo784226126e_bool)),
  file('Problems/SWW/SWW474+3.p',fact_562_Option_Oset_Osimps_I2_J)).
fof(f1201,axiom,(
  ! [X0] : dom_pname_com(X0) = hAPP_f759274231e_bool(collect_pname,hAPP_f759274231e_bool(cOMBB_647938656_pname(fNot),hAPP_o1092643708e_bool(hAPP_f837293113e_bool(cOMBC_1381995473m_bool,hAPP_f919496731m_bool(cOMBB_418828222_pname(fequal_option_com),X0)),none_com)))),
  file('Problems/SWW/SWW474+3.p',fact_1118_dom__def)).
fof(f1434,axiom,(
  hBOOL(hoare_1795711768gleton)),
  file('Problems/SWW/SWW474+3.p',conj_0)).
fof(f1435,axiom,(
  hBOOL(wT_bodies)),
  file('Problems/SWW/SWW474+3.p',conj_1)).
fof(f1439,axiom,(
  hAPP_p799580910on_com(body,pn) = hAPP_com_option_com(some_com,y)),
  file('Problems/SWW/SWW474+3.p',conj_5)).
fof(f1441,conjecture,(
  hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(hAPP_f360545851e_bool(image_185131637_state(hAPP_f1377420673_state(cOMBB_271860050_pname(hoare_Mirabelle_MGT),body_1)),dom_pname_com(body))),hAPP_f806699093e_bool(hAPP_H1902130436e_bool(insert1744391420_state,hAPP_c1455475371_state(hoare_Mirabelle_MGT,y)),bot_bo784226126e_bool)))),
  file('Problems/SWW/SWW474+3.p',conj_7)).
fof(f1442,negated_conjecture,(
  ~hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(hAPP_f360545851e_bool(image_185131637_state(hAPP_f1377420673_state(cOMBB_271860050_pname(hoare_Mirabelle_MGT),body_1)),dom_pname_com(body))),hAPP_f806699093e_bool(hAPP_H1902130436e_bool(insert1744391420_state,hAPP_c1455475371_state(hoare_Mirabelle_MGT,y)),bot_bo784226126e_bool)))),
  inference(negated_conjecture,[status(cth)],[f1441])).
fof(f1454,plain,(
  ~hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(hAPP_f360545851e_bool(image_185131637_state(hAPP_f1377420673_state(cOMBB_271860050_pname(hoare_Mirabelle_MGT),body_1)),dom_pname_com(body))),hAPP_f806699093e_bool(hAPP_H1902130436e_bool(insert1744391420_state,hAPP_c1455475371_state(hoare_Mirabelle_MGT,y)),bot_bo784226126e_bool)))),
  inference(flattening,[status(thm)],[f1442])).
fof(f1480,plain,(
  ! [X0,X1,X2] : ((hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(X0),X2)) | ~hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(X0),X1))) | ~hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(X1),X2)))),
  inference(ennf_transformation,[status(thm)],[f87])).
fof(f1481,plain,(
  ! [X0,X1,X2] : (hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(X0),X2)) | ~hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(X0),X1)) | ~hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(X1),X2)))),
  inference(flattening,[status(thm)],[f1480])).
fof(f1550,plain,(
  ! [X0] : (((hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(bot_bo784226126e_bool),hAPP_f806699093e_bool(hAPP_H1902130436e_bool(insert1744391420_state,hAPP_c1455475371_state(hoare_Mirabelle_MGT,X0)),bot_bo784226126e_bool))) | ~hBOOL(hAPP_com_bool(wt,X0))) | ~hBOOL(wT_bodies)) | ~hBOOL(hoare_1795711768gleton))),
  inference(ennf_transformation,[status(thm)],[f149])).
fof(f1551,plain,(
  ! [X0] : (hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(bot_bo784226126e_bool),hAPP_f806699093e_bool(hAPP_H1902130436e_bool(insert1744391420_state,hAPP_c1455475371_state(hoare_Mirabelle_MGT,X0)),bot_bo784226126e_bool))) | ~hBOOL(hAPP_com_bool(wt,X0)) | ~hBOOL(wT_bodies) | ~hBOOL(hoare_1795711768gleton))),
  inference(flattening,[status(thm)],[f1550])).
fof(f1721,plain,(
  ! [X0,X1] : ((hBOOL(hAPP_com_bool(wt,X1)) | hAPP_p799580910on_com(body,X0) != hAPP_com_option_com(some_com,X1)) | ~hBOOL(wT_bodies))),
  inference(ennf_transformation,[status(thm)],[f380])).
fof(f1722,plain,(
  ! [X0,X1] : (hBOOL(hAPP_com_bool(wt,X1)) | hAPP_p799580910on_com(body,X0) != hAPP_com_option_com(some_com,X1) | ~hBOOL(wT_bodies))),
  inference(flattening,[status(thm)],[f1721])).
fof(f3214,plain,(
  ( ! [X0] : (hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(X0),bot_bo784226126e_bool))) )),
  inference(cnf_transformation,[status(thm)],[f83])).
fof(f3218,plain,(
  ( ! [X2,X0,X1] : (~hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(X1),X2)) | ~hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(X0),X1)) | hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(X0),X2))) )),
  inference(cnf_transformation,[status(thm)],[f1481])).
fof(f3289,plain,(
  ( ! [X0] : (hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(bot_bo784226126e_bool),hAPP_f806699093e_bool(hAPP_H1902130436e_bool(insert1744391420_state,hAPP_c1455475371_state(hoare_Mirabelle_MGT,X0)),bot_bo784226126e_bool))) | ~hBOOL(hAPP_com_bool(wt,X0)) | ~hBOOL(wT_bodies) | ~hBOOL(hoare_1795711768gleton)) )),
  inference(cnf_transformation,[status(thm)],[f1551])).
fof(f3557,plain,(
  ( ! [X0] : (hAPP_f806699093e_bool(collec637225377_state,X0) = X0) )),
  inference(cnf_transformation,[status(thm)],[f323])).
fof(f3636,plain,(
  ( ! [X0] : (hAPP_f806699093e_bool(hAPP_H1902130436e_bool(insert1744391420_state,X0),bot_bo784226126e_bool) = hAPP_f806699093e_bool(collec637225377_state,hAPP_H216526335e_bool(fequal1440809015_state,X0))) )),
  inference(cnf_transformation,[status(thm)],[f378])).
fof(f3640,plain,(
  ( ! [X0,X1] : (hBOOL(hAPP_com_bool(wt,X1)) | hAPP_p799580910on_com(body,X0) != hAPP_com_option_com(some_com,X1) | ~hBOOL(wT_bodies)) )),
  inference(cnf_transformation,[status(thm)],[f1722])).
fof(f4177,plain,(
  ( ! [X0] : (hAPP_f806699093e_bool(hAPP_H1902130436e_bool(insert1744391420_state,X0),bot_bo784226126e_bool) = set_Ho1741238126_state(hAPP_H1633077406_state(some_H1043067815_state,X0))) )),
  inference(cnf_transformation,[status(thm)],[f645])).
fof(f5066,plain,(
  ( ! [X0] : (dom_pname_com(X0) = hAPP_f759274231e_bool(collect_pname,hAPP_f759274231e_bool(cOMBB_647938656_pname(fNot),hAPP_o1092643708e_bool(hAPP_f837293113e_bool(cOMBC_1381995473m_bool,hAPP_f919496731m_bool(cOMBB_418828222_pname(fequal_option_com),X0)),none_com)))) )),
  inference(cnf_transformation,[status(thm)],[f1201])).
fof(f5336,plain,(
  hBOOL(hoare_1795711768gleton)),
  inference(cnf_transformation,[status(thm)],[f1434])).
fof(f5337,plain,(
  hBOOL(wT_bodies)),
  inference(cnf_transformation,[status(thm)],[f1435])).
fof(f5341,plain,(
  hAPP_p799580910on_com(body,pn) = hAPP_com_option_com(some_com,y)),
  inference(cnf_transformation,[status(thm)],[f1439])).
fof(f5343,plain,(
  ~hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(hAPP_f360545851e_bool(image_185131637_state(hAPP_f1377420673_state(cOMBB_271860050_pname(hoare_Mirabelle_MGT),body_1)),dom_pname_com(body))),hAPP_f806699093e_bool(hAPP_H1902130436e_bool(insert1744391420_state,hAPP_c1455475371_state(hoare_Mirabelle_MGT,y)),bot_bo784226126e_bool)))),
  inference(cnf_transformation,[status(thm)],[f1454])).
fof(f5366,plain,(
  ~hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(hAPP_f360545851e_bool(image_185131637_state(hAPP_f1377420673_state(cOMBB_271860050_pname(hoare_Mirabelle_MGT),body_1)),hAPP_f759274231e_bool(collect_pname,hAPP_f759274231e_bool(cOMBB_647938656_pname(fNot),hAPP_o1092643708e_bool(hAPP_f837293113e_bool(cOMBC_1381995473m_bool,hAPP_f919496731m_bool(cOMBB_418828222_pname(fequal_option_com),body)),none_com))))),hAPP_f806699093e_bool(hAPP_H1902130436e_bool(insert1744391420_state,hAPP_c1455475371_state(hoare_Mirabelle_MGT,y)),bot_bo784226126e_bool)))),
  inference(definition_unfolding,[status(thm)],[f5343,f5066])).
fof(f5918,plain,(
  ( ! [X0,X1] : (hAPP_p799580910on_com(body,X0) != hAPP_com_option_com(some_com,X1) | hBOOL(hAPP_com_bool(wt,X1))) )),
  inference(forward_subsumption_resolution,[status(thm)],[f3640,f5337])).
fof(f5922,plain,(
  ( ! [X0] : (hAPP_f806699093e_bool(collec637225377_state,hAPP_H216526335e_bool(fequal1440809015_state,X0)) = set_Ho1741238126_state(hAPP_H1633077406_state(some_H1043067815_state,X0))) )),
  inference(forward_demodulation,[status(thm)],[f3636,f4177])).
fof(f6022,plain,(
  ( ! [X0] : (hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(bot_bo784226126e_bool),hAPP_f806699093e_bool(hAPP_H1902130436e_bool(insert1744391420_state,hAPP_c1455475371_state(hoare_Mirabelle_MGT,X0)),bot_bo784226126e_bool))) | ~hBOOL(hAPP_com_bool(wt,X0)) | ~hBOOL(hoare_1795711768gleton)) )),
  inference(forward_subsumption_resolution,[status(thm)],[f3289,f5337])).
fof(f6086,plain,(
  ( ! [X0] : (hAPP_H216526335e_bool(fequal1440809015_state,X0) = set_Ho1741238126_state(hAPP_H1633077406_state(some_H1043067815_state,X0))) )),
  inference(forward_demodulation,[status(thm)],[f5922,f3557])).
fof(f6136,plain,(
  ( ! [X0] : (hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(bot_bo784226126e_bool),hAPP_f806699093e_bool(hAPP_H1902130436e_bool(insert1744391420_state,hAPP_c1455475371_state(hoare_Mirabelle_MGT,X0)),bot_bo784226126e_bool))) | ~hBOOL(hAPP_com_bool(wt,X0))) )),
  inference(forward_subsumption_resolution,[status(thm)],[f6022,f5336])).
fof(f6183,plain,(
  ( ! [X0] : (hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(bot_bo784226126e_bool),set_Ho1741238126_state(hAPP_H1633077406_state(some_H1043067815_state,hAPP_c1455475371_state(hoare_Mirabelle_MGT,X0))))) | ~hBOOL(hAPP_com_bool(wt,X0))) )),
  inference(forward_demodulation,[status(thm)],[f6136,f4177])).
fof(f6203,plain,(
  ( ! [X0] : (hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(bot_bo784226126e_bool),hAPP_H216526335e_bool(fequal1440809015_state,hAPP_c1455475371_state(hoare_Mirabelle_MGT,X0)))) | ~hBOOL(hAPP_com_bool(wt,X0))) )),
  inference(forward_demodulation,[status(thm)],[f6183,f6086])).
fof(f7220,plain,(
  ~hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(hAPP_f360545851e_bool(image_185131637_state(hAPP_f1377420673_state(cOMBB_271860050_pname(hoare_Mirabelle_MGT),body_1)),hAPP_f759274231e_bool(collect_pname,hAPP_f759274231e_bool(cOMBB_647938656_pname(fNot),hAPP_o1092643708e_bool(hAPP_f837293113e_bool(cOMBC_1381995473m_bool,hAPP_f919496731m_bool(cOMBB_418828222_pname(fequal_option_com),body)),none_com))))),set_Ho1741238126_state(hAPP_H1633077406_state(some_H1043067815_state,hAPP_c1455475371_state(hoare_Mirabelle_MGT,y)))))),
  inference(superposition,[status(thm)],[f5366,f4177])).
fof(f7227,plain,(
  ~hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(hAPP_f360545851e_bool(image_185131637_state(hAPP_f1377420673_state(cOMBB_271860050_pname(hoare_Mirabelle_MGT),body_1)),hAPP_f759274231e_bool(collect_pname,hAPP_f759274231e_bool(cOMBB_647938656_pname(fNot),hAPP_o1092643708e_bool(hAPP_f837293113e_bool(cOMBC_1381995473m_bool,hAPP_f919496731m_bool(cOMBB_418828222_pname(fequal_option_com),body)),none_com))))),hAPP_H216526335e_bool(fequal1440809015_state,hAPP_c1455475371_state(hoare_Mirabelle_MGT,y))))),
  inference(forward_demodulation,[status(thm)],[f7220,f6086])).
fof(f7506,plain,(
  ( ! [X0] : (hAPP_com_option_com(some_com,X0) != hAPP_com_option_com(some_com,y) | hBOOL(hAPP_com_bool(wt,X0))) )),
  inference(superposition,[status(thm)],[f5918,f5341])).
fof(f19061,plain,(
  ( ! [X0,X1] : (~hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(X0),bot_bo784226126e_bool)) | hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(X0),hAPP_H216526335e_bool(fequal1440809015_state,hAPP_c1455475371_state(hoare_Mirabelle_MGT,X1)))) | ~hBOOL(hAPP_com_bool(wt,X1))) )),
  inference(resolution,[status(thm)],[f3218,f6203])).
fof(f19072,plain,(
  ( ! [X0,X1] : (hBOOL(hAPP_f1378282496l_bool(hoare_512830354_state(X0),hAPP_H216526335e_bool(fequal1440809015_state,hAPP_c1455475371_state(hoare_Mirabelle_MGT,X1)))) | ~hBOOL(hAPP_com_bool(wt,X1))) )),
  inference(forward_subsumption_resolution,[status(thm)],[f19061,f3214])).
fof(f77710,plain,(
  hBOOL(hAPP_com_bool(wt,y))),
  inference(equality_resolution,[status(thm)],[f7506])).
fof(f107907,plain,(
  ~hBOOL(hAPP_com_bool(wt,y))),
  inference(resolution,[status(thm)],[f19072,f7227])).
fof(f107918,plain,(
  $false),
  inference(forward_subsumption_resolution,[status(thm)],[f107907,f77710])).
% SZS output end Proof for SWW474+3
% ------------------------------
% Version: Vampire 5.0.1 (Release build, commit 3f1362b99 on 2026-07-01 15:21:00 +0200)
% Linked with Z3 4.14.0.0 3c47fd96cf5645d0c42b2c819d9e9a84380aa721 z3-4.8.4-9178-g3c47fd96c
% CaDiCaL version: 2.1.3
% Termination reason: Refutation
% Time elapsed: 0.927 s
% Peak memory usage: 79 MB
% Instructions burned: 5647 (million)
% ------------------------------
% ------------------------------
