ZAbbreviation ("NatValue",[],"") (ZCall (ZVar ("\\upto",[],"")) (ZTuple [ZInt 0,ZInt 1]))
ZFreeTypeDef ("BUTTON",[],"") [ZBranch0 ("ON",[],""),ZBranch0 ("OFF",[],"")]
CircChannel [CChan "autSelfTest",CChan "atrialTubing"]
CircChannel [CChan "ventricularTubing",CChan "connectDialyzer"]
CircChannel [CChan "stopBloodFlow",CChan "produceAlarmSound",CChan "stopBP"]
CircChannel [CChan "disconnectDF",CChan "stopFlowDialyzer",CChan "stopCoagulantFlow"]
CircChannel [CChan "fillArterialDrip",CChan "connPatientArterially",CChan "connPatientVenously"]
CircChannel [CChan "insertHeparinSyringe",CChan "heparinLineIsVented"]
CircChannel [CChanDecl "connectingConcentrate" (ZVar ("BUTTON",[],""))]
CircChannel [CChanDecl "salineBagLevel" (ZVar ("NatValue",[],""))]
CircChannel [CChanDecl "senAirVol" (ZVar ("NatValue",[],""))]
CircChannel [CChanDecl "senAirVolLimit" (ZVar ("NatValue",[],""))]
CircChannel [CChanDecl "senApTransdPress" (ZVar ("NatValue",[],""))]
CircChannel [CChanDecl "senBloodFlowInEBC" (ZVar ("NatValue",[],""))]
CircChannel [CChanDecl "senBypassVol" (ZVar ("BUTTON",[],""))]
CircChannel [CChanDecl "senFflowDirect" (ZVar ("BUTTON",[],""))]
CircChannel [CChanDecl "senInfVol" (ZVar ("NatValue",[],""))]
CircChannel [CChanDecl "senLastNonZeroBF" (ZVar ("NatValue",[],""))]
CircChannel [CChanDecl "senNetFluidRemoval" (ZVar ("BUTTON",[],""))]
CircChannel [CChanDecl "senNetFluidRemovalRate" (ZVar ("NatValue",[],""))]
CircChannel [CChanDecl "senRotDirectBP" (ZVar ("BUTTON",[],""))]
CircChannel [CChanDecl "senRotDirectUFP" (ZVar ("BUTTON",[],""))]
CircChannel [CChanDecl "senVolInEBC" (ZVar ("NatValue",[],""))]
CircChannel [CChanDecl "senVpTransdPress" (ZVar ("NatValue",[],""))]
CircChannel [CChanDecl "senSADSensorFlow" (ZVar ("NatValue",[],""))]
CircChannel [CChanDecl "senHDMode" (ZVar ("BUTTON",[],""))]
CircChannel [CChanDecl "getCurrentTime" (ZVar ("NatValue",[],""))]
CircChannel [CChan "tick",CChan "connectThePatient",CChan "initPhase",CChan "prepPhase",CChan "endPhase",CChan "applicationArterialBolus",CChan "rinsing",CChan "idle"]
CircChannel [CChan "preparationPhase",CChan "connectingToPatient",CChan "therapyInitiation",CChan "therapyEnding"]
CircChannel [CChanDecl "setRinsingParameters" (ZCross [ZVar ("NatValue",[],""),ZVar ("NatValue",[],""),ZVar ("NatValue",[],""),ZVar ("NatValue",[],""),ZVar ("NatValue",[],""),ZVar ("NatValue",[],"")])]
CircChannel [CChanDecl "setDFParameters" (ZCross [ZVar ("NatValue",[],""),ZVar ("BUTTON",[],""),ZVar ("NatValue",[],""),ZVar ("NatValue",[],""),ZVar ("NatValue",[],""),ZVar ("NatValue",[],"")])]
CircChannel [CChanDecl "setRinsingBPSpeed" (ZVar ("NatValue",[],""))]
CircChannel [CChanDecl "setUFParameters" (ZCross [ZVar ("NatValue",[],""),ZVar ("NatValue",[],""),ZVar ("NatValue",[],""),ZVar ("NatValue",[],"")])]
CircChannel [CChanDecl "setMinUFRateTreat" (ZVar ("BUTTON",[],""))]
CircChannel [CChanDecl "setArtBolusVol" (ZVar ("NatValue",[],""))]
CircChannel [CChan "setBloodLines"]
CircChannel [CChanDecl "setPressureParameters" (ZCross [ZVar ("NatValue",[],""),ZVar ("NatValue",[],""),ZVar ("BUTTON",[],""),ZVar ("NatValue",[],""),ZVar ("BUTTON",[],"")])]
CircChannel [CChan "endTreatment"]
ZSchemaDef (ZSPlain "HDGenComp") (ZSchema [Choose ("airVolLimit",[],"") (ZVar ("NatValue",[],"")),Choose ("airVol",[],"") (ZVar ("NatValue",[],"")),Choose ("alarm",[],"") (ZVar ("BUTTON",[],"")),Choose ("artBolusVol",[],"") (ZVar ("NatValue",[],"")),Choose ("apTransdPress",[],"") (ZVar ("NatValue",[],"")),Choose ("bloodFlowInEBC",[],"") (ZVar ("NatValue",[],"")),Choose ("bypassValve",[],"") (ZVar ("BUTTON",[],"")),Choose ("fflowDirect",[],"") (ZVar ("BUTTON",[],"")),Choose ("hdMode",[],"") (ZVar ("BUTTON",[],"")),Choose ("infSalineVol",[],"") (ZVar ("NatValue",[],"")),Choose ("lastNonZeroBF",[],"") (ZVar ("NatValue",[],"")),Choose ("lowerPressureLimit",[],"") (ZVar ("NatValue",[],"")),Choose ("netFluidRemovalRate",[],"") (ZVar ("NatValue",[],"")),Choose ("netFluidRemoval",[],"") (ZVar ("BUTTON",[],"")),Choose ("rotDirectionBP",[],"") (ZVar ("BUTTON",[],"")),Choose ("rotDirectionUFP",[],"") (ZVar ("BUTTON",[],"")),Choose ("safeUpperLimit",[],"") (ZVar ("NatValue",[],"")),Choose ("timerIntervalR9",[],"") (ZVar ("NatValue",[],"")),Choose ("timerIntervalR10",[],"") (ZVar ("NatValue",[],"")),Choose ("timerIntervalR11",[],"") (ZVar ("NatValue",[],"")),Choose ("timerIntervalR12",[],"") (ZVar ("NatValue",[],"")),Choose ("timerIntervalR13",[],"") (ZVar ("NatValue",[],"")),Choose ("time",[],"") (ZVar ("NatValue",[],"")),Choose ("upperPressureLimit",[],"") (ZVar ("NatValue",[],"")),Choose ("volumeInEBC",[],"") (ZVar ("NatValue",[],"")),Choose ("vpTransdPress",[],"") (ZVar ("NatValue",[],"")),Choose ("sadSensorFlow",[],"") (ZVar ("NatValue",[],"")),Choose ("bloodLines",[],"") (ZVar ("BUTTON",[],"")),Choose ("signalLamp",[],"") (ZVar ("BUTTON",[],"")),Choose ("minUFRateTreat",[],"") (ZVar ("BUTTON",[],""))])
ZSchemaDef (ZSPlain "RinsingParameters") (ZSchema [Choose ("fillingBPRate",[],"") (ZVar ("NatValue",[],"")),Choose ("rinsingBPRate",[],"") (ZVar ("NatValue",[],"")),Choose ("rinsingTime",[],"") (ZVar ("NatValue",[],"")),Choose ("ufRateForRinsing",[],"") (ZVar ("NatValue",[],"")),Choose ("ufVolForRinsing",[],"") (ZVar ("NatValue",[],"")),Choose ("bloodFlowForConnectingPatient",[],"") (ZVar ("NatValue",[],""))])
ZSchemaDef (ZSPlain "DFParameters") (ZSchema [Choose ("conductivity",[],"") (ZVar ("NatValue",[],"")),Choose ("bicarbonateAcetate",[],"") (ZVar ("BUTTON",[],"")),Choose ("bicarbonateConductivity",[],"") (ZVar ("NatValue",[],"")),Choose ("dfTemperature",[],"") (ZVar ("NatValue",[],"")),Choose ("rinsingTime",[],"") (ZVar ("NatValue",[],"")),Choose ("dfFlow",[],"") (ZVar ("NatValue",[],""))])
ZSchemaDef (ZSPlain "UFParameters") (ZSchema [Choose ("ufVol",[],"") (ZVar ("NatValue",[],"")),Choose ("therapyTime",[],"") (ZVar ("NatValue",[],"")),Choose ("minUFRate",[],"") (ZVar ("NatValue",[],"")),Choose ("maxUFRate",[],"") (ZVar ("NatValue",[],""))])
ZSchemaDef (ZSPlain "PressureParameters") (ZSchema [Choose ("limitDeltaMinMaxAP",[],"") (ZVar ("NatValue",[],"")),Choose ("actualTMPMaxTMP",[],"") (ZVar ("NatValue",[],"")),Choose ("limitsTMP",[],"") (ZVar ("BUTTON",[],"")),Choose ("lowHigh",[],"") (ZVar ("NatValue",[],"")),Choose ("extendedTMPLimitRange",[],"") (ZVar ("BUTTON",[],""))])
Assert "HDEnv = ( ( HDMachine(b_NAT1,b_BUT1) [| {| tick,getCurrentTime |} |] SysClock(b_NAT1) ) \\ {| tick,getCurrentTime |} )"
Assert "MyHDMACHINE = let X = HDMachine(b_NAT1,b_BUT1); X within X"
Assert "assert HDMachine(b_NAT1,b_BUT1) :[ deadlock free [FD] ]"
Assert "assert HDMachine(b_NAT1,b_BUT1) :[ livelock free ]"
Assert "assert HDMachine(b_NAT1,b_BUT1) :[ deterministic [F] ]"
ZFreeTypeDef ("UNIVERSE",[],"") [ZBranch1 ("BUT",[],"") (ZVar ("BUTTON",[],"")),ZBranch1 ("NAT",[],"") (ZVar ("NatValue",[],""))]
ZFreeTypeDef ("U_BUT",[],"") [ZBranch1 ("BUT",[],"") (ZVar ("BUTTON",[],""))]
ZFreeTypeDef ("U_NAT",[],"") [ZBranch1 ("NAT",[],"") (ZVar ("NatValue",[],""))]
ZFreeTypeDef ("NAME",[],"") [ZBranch0 ("sv_airVolLimit",[],"NAT"),ZBranch0 ("sv_airVol",[],"NAT"),ZBranch0 ("sv_alarm",[],"BUT"),ZBranch0 ("sv_artBolusVol",[],"NAT"),ZBranch0 ("sv_apTransdPress",[],"NAT"),ZBranch0 ("sv_bloodFlowInEBC",[],"NAT"),ZBranch0 ("sv_bypassValve",[],"BUT"),ZBranch0 ("sv_fflowDirect",[],"BUT"),ZBranch0 ("sv_hdMode",[],"BUT"),ZBranch0 ("sv_infSalineVol",[],"NAT"),ZBranch0 ("sv_lastNonZeroBF",[],"NAT"),ZBranch0 ("sv_lowerPressureLimit",[],"NAT"),ZBranch0 ("sv_netFluidRemovalRate",[],"NAT"),ZBranch0 ("sv_netFluidRemoval",[],"BUT"),ZBranch0 ("sv_rotDirectionBP",[],"BUT"),ZBranch0 ("sv_rotDirectionUFP",[],"BUT"),ZBranch0 ("sv_safeUpperLimit",[],"NAT"),ZBranch0 ("sv_timerIntervalR9",[],"NAT"),ZBranch0 ("sv_timerIntervalR10",[],"NAT"),ZBranch0 ("sv_timerIntervalR11",[],"NAT"),ZBranch0 ("sv_timerIntervalR12",[],"NAT"),ZBranch0 ("sv_timerIntervalR13",[],"NAT"),ZBranch0 ("sv_upperPressureLimit",[],"NAT"),ZBranch0 ("sv_volumeInEBC",[],"NAT"),ZBranch0 ("sv_vpTransdPress",[],"NAT"),ZBranch0 ("sv_sadSensorFlow",[],"NAT"),ZBranch0 ("sv_bloodLines",[],"BUT"),ZBranch0 ("sv_signalLamp",[],"BUT"),ZBranch0 ("sv_minUFRateTreat",[],"BUT"),ZBranch0 ("sv_fillingBPRate",[],"NAT"),ZBranch0 ("sv_rinsingBPRate",[],"NAT"),ZBranch0 ("sv_ufRateForRinsing",[],"NAT"),ZBranch0 ("sv_ufVolForRinsing",[],"NAT"),ZBranch0 ("sv_bloodFlowForConnectingPatient",[],"NAT"),ZBranch0 ("sv_conductivity",[],"NAT"),ZBranch0 ("sv_bicarbonateAcetate",[],"BUT"),ZBranch0 ("sv_bicarbonateConductivity",[],"NAT"),ZBranch0 ("sv_dfTemperature",[],"NAT"),ZBranch0 ("sv_rinsingTime",[],"NAT"),ZBranch0 ("sv_dfFlow",[],"NAT"),ZBranch0 ("sv_ufVol",[],"NAT"),ZBranch0 ("sv_therapyTime",[],"NAT"),ZBranch0 ("sv_minUFRate",[],"NAT"),ZBranch0 ("sv_maxUFRate",[],"NAT"),ZBranch0 ("sv_limitDeltaMinMaxAP",[],"NAT"),ZBranch0 ("sv_actualTMPMaxTMP",[],"NAT"),ZBranch0 ("sv_limitsTMP",[],"BUT"),ZBranch0 ("sv_lowHigh",[],"NAT"),ZBranch0 ("sv_extendedTMPLimitRange",[],"BUT"),ZBranch0 ("sv_time",[],"NAT")]
ZFreeTypeDef ("NAME_NAT",[],"") [ZBranch0 ("sv_airVolLimit",[],"NAT"),ZBranch0 ("sv_airVol",[],"NAT"),ZBranch0 ("sv_artBolusVol",[],"NAT"),ZBranch0 ("sv_apTransdPress",[],"NAT"),ZBranch0 ("sv_bloodFlowInEBC",[],"NAT"),ZBranch0 ("sv_infSalineVol",[],"NAT"),ZBranch0 ("sv_lastNonZeroBF",[],"NAT"),ZBranch0 ("sv_lowerPressureLimit",[],"NAT"),ZBranch0 ("sv_netFluidRemovalRate",[],"NAT"),ZBranch0 ("sv_safeUpperLimit",[],"NAT"),ZBranch0 ("sv_timerIntervalR9",[],"NAT"),ZBranch0 ("sv_timerIntervalR10",[],"NAT"),ZBranch0 ("sv_timerIntervalR11",[],"NAT"),ZBranch0 ("sv_timerIntervalR12",[],"NAT"),ZBranch0 ("sv_timerIntervalR13",[],"NAT"),ZBranch0 ("sv_time",[],"NAT"),ZBranch0 ("sv_upperPressureLimit",[],"NAT"),ZBranch0 ("sv_volumeInEBC",[],"NAT"),ZBranch0 ("sv_vpTransdPress",[],"NAT"),ZBranch0 ("sv_sadSensorFlow",[],"NAT"),ZBranch0 ("sv_fillingBPRate",[],"NAT"),ZBranch0 ("sv_rinsingBPRate",[],"NAT"),ZBranch0 ("sv_rinsingTime",[],"NAT"),ZBranch0 ("sv_ufRateForRinsing",[],"NAT"),ZBranch0 ("sv_ufVolForRinsing",[],"NAT"),ZBranch0 ("sv_bloodFlowForConnectingPatient",[],"NAT"),ZBranch0 ("sv_conductivity",[],"NAT"),ZBranch0 ("sv_bicarbonateConductivity",[],"NAT"),ZBranch0 ("sv_dfTemperature",[],"NAT"),ZBranch0 ("sv_rinsingTime",[],"NAT"),ZBranch0 ("sv_dfFlow",[],"NAT"),ZBranch0 ("sv_ufVol",[],"NAT"),ZBranch0 ("sv_therapyTime",[],"NAT"),ZBranch0 ("sv_minUFRate",[],"NAT"),ZBranch0 ("sv_maxUFRate",[],"NAT"),ZBranch0 ("sv_limitDeltaMinMaxAP",[],"NAT"),ZBranch0 ("sv_actualTMPMaxTMP",[],"NAT"),ZBranch0 ("sv_lowHigh",[],"NAT"),ZBranch0 ("sv_time",[],"NAT")]
ZFreeTypeDef ("NAME_BUT",[],"") [ZBranch0 ("sv_alarm",[],"BUT"),ZBranch0 ("sv_bypassValve",[],"BUT"),ZBranch0 ("sv_fflowDirect",[],"BUT"),ZBranch0 ("sv_hdMode",[],"BUT"),ZBranch0 ("sv_netFluidRemoval",[],"BUT"),ZBranch0 ("sv_rotDirectionBP",[],"BUT"),ZBranch0 ("sv_rotDirectionUFP",[],"BUT"),ZBranch0 ("sv_bloodLines",[],"BUT"),ZBranch0 ("sv_signalLamp",[],"BUT"),ZBranch0 ("sv_minUFRateTreat",[],"BUT"),ZBranch0 ("sv_bicarbonateAcetate",[],"BUT"),ZBranch0 ("sv_limitsTMP",[],"BUT"),ZBranch0 ("sv_extendedTMPLimitRange",[],"BUT")]
ZAbbreviation ("BINDINGS_NAT",[],"") (ZCall (ZVar ("\\fun",[],"")) (ZTuple [ZVar ("NAME_NAT",[],""),ZVar ("U_NAT",[],"")]))
ZAbbreviation ("BINDINGS_BUT",[],"") (ZCall (ZVar ("\\fun",[],"")) (ZTuple [ZVar ("NAME_BUT",[],""),ZVar ("U_BUT",[],"")]))
ZAbbreviation ("BINDINGS",[],"") (ZCall (ZVar ("\\cup",[],"")) (ZTuple [ZVar ("BINDINGS_BUT",[],""),ZVar ("BINDINGS_NAT",[],"")]))
ZAbbreviation ("\\delta_NAT",[],"") (ZSetDisplay [ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_airVolLimit",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_airVol",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_artBolusVol",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_apTransdPress",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_bloodFlowInEBC",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_infSalineVol",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_lastNonZeroBF",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_lowerPressureLimit",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_netFluidRemovalRate",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_safeUpperLimit",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_timerIntervalR9",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_timerIntervalR10",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_timerIntervalR11",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_timerIntervalR12",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_timerIntervalR13",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_time",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_upperPressureLimit",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_volumeInEBC",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_vpTransdPress",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_sadSensorFlow",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_fillingBPRate",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_rinsingBPRate",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_rinsingTime",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_ufRateForRinsing",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_ufVolForRinsing",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_bloodFlowForConnectingPatient",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_conductivity",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_bicarbonateConductivity",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_dfTemperature",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_rinsingTime",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_dfFlow",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_ufVol",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_therapyTime",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_minUFRate",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_maxUFRate",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_limitDeltaMinMaxAP",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_actualTMPMaxTMP",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_lowHigh",[],"NAT"),ZVar ("NatValue",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_time",[],"NAT"),ZVar ("NatValue",[],"")])])
ZAbbreviation ("\\delta_BUT",[],"") (ZSetDisplay [ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_alarm",[],"BUT"),ZVar ("BUTTON",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_bypassValve",[],"BUT"),ZVar ("BUTTON",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_fflowDirect",[],"BUT"),ZVar ("BUTTON",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_hdMode",[],"BUT"),ZVar ("BUTTON",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_netFluidRemoval",[],"BUT"),ZVar ("BUTTON",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_rotDirectionBP",[],"BUT"),ZVar ("BUTTON",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_rotDirectionUFP",[],"BUT"),ZVar ("BUTTON",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_bloodLines",[],"BUT"),ZVar ("BUTTON",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_signalLamp",[],"BUT"),ZVar ("BUTTON",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_minUFRateTreat",[],"BUT"),ZVar ("BUTTON",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_bicarbonateAcetate",[],"BUT"),ZVar ("BUTTON",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_limitsTMP",[],"BUT"),ZVar ("BUTTON",[],"")]),ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("sv_extendedTMPLimitRange",[],"BUT"),ZVar ("BUTTON",[],"")])])
CircChannel [CChanDecl "mget" (ZCross [ZVar ("NAME",[],""),ZVar ("UNIVERSE",[],"")]),CChanDecl "mset" (ZCross [ZVar ("NAME",[],""),ZVar ("UNIVERSE",[],"")])]
CircChannel [CChan "terminate"]
CircChanSet "MEMI" (CChanSet ["mset","mget","terminate"])
CircChannel [CChanDecl "lget" (ZCross [ZVar ("NAME",[],""),ZVar ("UNIVERSE",[],"")]),CChanDecl "lset" (ZCross [ZVar ("NAME",[],""),ZVar ("UNIVERSE",[],"")])]
CircChannel [CChan "lterminate"]
CircChanSet "MEML" (CChanSet ["lset","lget","lterminate"])
Process (CProcess "HDMachine" (ProcDef (ProcStalessMain [CParAction "Memory" (CircusAction (CActionCommand (CVResDecl [Choose ("b_NAT",[],"") (ZVar ("BINDING_NAT",[],"")),Choose ("b_BUT",[],"") (ZVar ("BINDING_BUT",[],""))] (CSPExtChoice (CSPExtChoice (CSPExtChoice (CSPRepExtChoice [Choose ("n",[],"NAT") (ZCall (ZVar ("\\dom",[],"")) (ZVar ("b_NAT",[],"")))] (CSPCommAction (ChanComm "mget" [ChanDotExp (ZVar ("n",[],"NAT")),ChanOutExp (ZCall (ZVar ("b_NAT",[],"")) (ZVar ("n",[],"NAT")))]) (CSPParAction "Memory" [ZVar ("b_NAT",[],""),ZVar ("b_BUT",[],"")]))) (CSPRepExtChoice [Choose ("n",[],"BUT") (ZCall (ZVar ("\\dom",[],"")) (ZVar ("b_BUT",[],"")))] (CSPCommAction (ChanComm "mget" [ChanDotExp (ZVar ("n",[],"BUT")),ChanOutExp (ZCall (ZVar ("b_BUT",[],"")) (ZVar ("n",[],"BUT")))]) (CSPParAction "Memory" [ZVar ("b_NAT",[],""),ZVar ("b_BUT",[],"")])))) (CSPExtChoice (CSPRepExtChoice [Choose ("n",[],"NAT") (ZCall (ZVar ("\\dom",[],"")) (ZVar ("b_NAT",[],"")))] (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("n",[],"NAT")),ChanInpPred "nv" (ZMember (ZVar ("nv",[],"NAT")) (ZCall (ZVar ("\\delta",[],"")) (ZVar ("n",[],"NAT"))))]) (CSPParAction "Memory" [ZCall (ZVar ("\\oplus",[],"")) (ZTuple [ZVar ("b_NAT",[],""),ZSetDisplay [ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("n",[],""),ZVar ("nv",[],"")])]]),ZVar ("b_BUT",[],"")]))) (CSPRepExtChoice [Choose ("n",[],"BUT") (ZCall (ZVar ("\\dom",[],"")) (ZVar ("b_BUT",[],"")))] (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("n",[],"b_BUT")),ChanInpPred "nv" (ZMember (ZVar ("nv",[],"BUT")) (ZCall (ZVar ("\\delta",[],"")) (ZVar ("n",[],"BUT"))))]) (CSPParAction "Memory" [ZVar ("b_NAT",[],""),ZCall (ZVar ("\\oplus",[],"")) (ZTuple [ZVar ("b_BUT",[],""),ZSetDisplay [ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("n",[],""),ZVar ("nv",[],"")])]])]))))) (CSPCommAction (ChanComm "terminate" []) CSPSkip))))),CParAction "MemoryMerge" (CircusAction (CActionCommand (CVResDecl [Choose ("b_NAT",[],"") (ZVar ("BINDING_NAT",[],"")),Choose ("b_BUT",[],"") (ZVar ("BINDING_BUT",[],"")),Choose ("ns",[],"") (ZCall (ZVar ("\\seq",[],"")) (ZVar ("NAME",[],"")))] (CSPExtChoice (CSPExtChoice (CSPExtChoice (CSPRepExtChoice [Choose ("n",[],"NAT") (ZCall (ZVar ("\\dom",[],"")) (ZVar ("b_NAT",[],"")))] (CSPCommAction (ChanComm "lget" [ChanDotExp (ZVar ("n",[],"NAT")),ChanOutExp (ZCall (ZVar ("b_NAT",[],"")) (ZVar ("n",[],"NAT")))]) (CSPParAction "MemoryMerge" [ZVar ("b_NAT",[],""),ZVar ("b_BUT",[],""),ZVar ("ns",[],"")]))) (CSPRepExtChoice [Choose ("n",[],"BUT") (ZCall (ZVar ("\\dom",[],"")) (ZVar ("b_BUT",[],"")))] (CSPCommAction (ChanComm "lget" [ChanDotExp (ZVar ("n",[],"BUT")),ChanOutExp (ZCall (ZVar ("b_BUT",[],"")) (ZVar ("n",[],"BUT")))]) (CSPParAction "MemoryMerge" [ZVar ("b_NAT",[],""),ZVar ("b_BUT",[],""),ZVar ("ns",[],"")])))) (CSPExtChoice (CSPRepExtChoice [Choose ("n",[],"NAT") (ZCall (ZVar ("\\dom",[],"")) (ZVar ("b_NAT",[],"")))] (CSPCommAction (ChanComm "lset" [ChanDotExp (ZVar ("n",[],"NAT")),ChanInpPred "nv" (ZMember (ZVar ("nv",[],"NAT")) (ZCall (ZVar ("\\delta",[],"")) (ZVar ("n",[],"NAT"))))]) (CSPParAction "MemoryMerge" [ZCall (ZVar ("\\oplus",[],"")) (ZTuple [ZVar ("b_NAT",[],""),ZSetDisplay [ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("n",[],""),ZVar ("nv",[],"")])]]),ZVar ("b_BUT",[],""),ZVar ("ns",[],"")]))) (CSPRepExtChoice [Choose ("n",[],"BUT") (ZCall (ZVar ("\\dom",[],"")) (ZVar ("b_BUT",[],"")))] (CSPCommAction (ChanComm "lset" [ChanDotExp (ZVar ("n",[],"BUT")),ChanInpPred "nv" (ZMember (ZVar ("nv",[],"BUT")) (ZCall (ZVar ("\\delta",[],"")) (ZVar ("n",[],"BUT"))))]) (CSPParAction "MemoryMerge" [ZVar ("b_NAT",[],""),ZCall (ZVar ("\\oplus",[],"")) (ZTuple [ZVar ("b_BUT",[],""),ZSetDisplay [ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("n",[],""),ZVar ("nv",[],"")])]]),ZVar ("ns",[],"")]))))) (CSPCommAction (ChanComm "lterminate" []) (CSPRepSeq [Choose ("bd",[],"") (ZSeqDisplay [ZCall (ZVar ("\\cup",[],"")) (ZTuple [ZVar ("b_NAT",[],""),ZVar ("b_BUT",[],"")])]),Choose ("n",[],"") (ZSeqDisplay [ZVar ("ns",[],"")])] (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("n",[],"")),ChanOutExp (ZCall (ZVar ("bd",[],"")) (ZVar ("n",[],"")))]) CSPSkip)))))))] (CSPRepIntChoice [Choose ("b_NAT",[],"") (ZVar ("BINDING_NAT",[],"")),Choose ("b_BUT",[],"") (ZVar ("BINDING_BUT",[],""))] (CSPHide (CSPNSParal [] (CSExpr "MEMI") [ZVar ("b_NAT",[],""),ZVar ("b_BUT",[],"")] (CSPSeq (CSPCommAction (ChanComm "prepPhase" []) (CSPCommAction (ChanComm "autSelfTest" []) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_signalLamp",[],"BUT")),ChanDotExp (ZVar ("ON",[],""))]) (CSPCommAction (ChanComm "connectingConcentrate" [ChanInp "t_sv_bicarbonateAcetate"]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_bicarbonateAcetate",[],"BUT")),ChanDotExp (ZVar ("t_sv_bicarbonateAcetate",[],""))]) (CSPCommAction (ChanComm "setRinsingParameters" [ChanInp "t_sv_fillingBPRate",ChanInp "t_sv_rinsingBPRate",ChanInp "t_sv_rinsingTime",ChanInp "t_sv_ufRateForRinsing",ChanInp "t_sv_ufVolForRinsing",ChanInp "t_sv_bloodFlowForConnectingPatient"]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_fillingBPRate",[],"NAT")),ChanDotExp (ZVar ("t_sv_fillingBPRate",[],""))]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_rinsingBPRate",[],"NAT")),ChanDotExp (ZVar ("t_sv_rinsingBPRate",[],""))]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_rinsingTime",[],"NAT")),ChanDotExp (ZVar ("t_sv_rinsingTime",[],""))]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_ufRateForRinsing",[],"NAT")),ChanDotExp (ZVar ("t_sv_ufRateForRinsing",[],""))]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_ufVolForRinsing",[],"NAT")),ChanDotExp (ZVar ("t_sv_ufVolForRinsing",[],""))]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_bloodFlowForConnectingPatient",[],"NAT")),ChanDotExp (ZVar ("t_sv_bloodFlowForConnectingPatient",[],""))]) (CSPSeq (CSPSeq (CSPSeq (CSPSeq (CSPSeq (CSPSeq (CSPSeq (CSPSeq (CSPInterleave (CSPCommAction (ChanComm "atrialTubing" []) CSPSkip) (CSPCommAction (ChanComm "ventricularTubing" []) CSPSkip)) (CSPCommAction (ChanComm "salineBagLevel" [ChanInp "t_sv_infSalineVol"]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_infSalineVol",[],"NAT")),ChanDotExp (ZVar ("t_sv_infSalineVol",[],""))]) CSPSkip))) (CSPCommAction (ChanComm "setBloodLines" []) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_bloodLines",[],"BUT")),ChanDotExp (ZVar ("ON",[],""))]) CSPSkip))) (CSPCommAction (ChanComm "setRinsingBPSpeed" [ChanInp "t_sv_rinsingBPRate"]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_rinsingBPRate",[],"NAT")),ChanDotExp (ZVar ("t_sv_rinsingBPRate",[],""))]) CSPSkip))) (CSPCommAction (ChanComm "insertHeparinSyringe" []) (CSPCommAction (ChanComm "heparinLineIsVented" []) CSPSkip))) (CSPCommAction (ChanComm "setDFParameters" [ChanInp "t_sv_conductivity",ChanInp "t_sv_bicarbonateAcetate",ChanInp "t_sv_bicarbonateConductivity",ChanInp "t_sv_dfTemperature",ChanInp "t_sv_rinsingTime",ChanInp "t_sv_dfFlow"]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_conductivity",[],"NAT")),ChanDotExp (ZVar ("t_sv_conductivity",[],""))]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_bicarbonateAcetate",[],"BUT")),ChanDotExp (ZVar ("t_sv_bicarbonateAcetate",[],""))]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_bicarbonateConductivity",[],"NAT")),ChanDotExp (ZVar ("t_sv_bicarbonateConductivity",[],""))]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_dfTemperature",[],"NAT")),ChanDotExp (ZVar ("t_sv_dfTemperature",[],""))]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_rinsingTime",[],"NAT")),ChanDotExp (ZVar ("t_sv_rinsingTime",[],""))]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_dfFlow",[],"NAT")),ChanDotExp (ZVar ("t_sv_dfFlow",[],""))]) (CSPCommAction (ChanComm "setUFParameters" [ChanInp "t_sv_ufVol",ChanInp "t_sv_therapyTime",ChanInp "t_sv_minUFRate",ChanInp "t_sv_maxUFRate"]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_ufVol",[],"NAT")),ChanDotExp (ZVar ("t_sv_ufVol",[],""))]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_therapyTime",[],"NAT")),ChanDotExp (ZVar ("t_sv_therapyTime",[],""))]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_minUFRate",[],"NAT")),ChanDotExp (ZVar ("t_sv_minUFRate",[],""))]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_maxUFRate",[],"NAT")),ChanDotExp (ZVar ("t_sv_maxUFRate",[],""))]) (CSPCommAction (ChanComm "setPressureParameters" [ChanInp "t_sv_limitDeltaMinMaxAP",ChanInp "t_sv_actualTMPMaxTMP",ChanInp "t_sv_limitsTMP",ChanInp "t_sv_lowHigh",ChanInp "t_sv_extendedTMPLimitRange"]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_limitDeltaMinMaxAP",[],"NAT")),ChanDotExp (ZVar ("t_sv_limitDeltaMinMaxAP",[],""))]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_actualTMPMaxTMP",[],"NAT")),ChanDotExp (ZVar ("t_sv_actualTMPMaxTMP",[],""))]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_limitsTMP",[],"BUT")),ChanDotExp (ZVar ("t_sv_limitsTMP",[],""))]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_lowHigh",[],"NAT")),ChanDotExp (ZVar ("t_sv_lowHigh",[],""))]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_extendedTMPLimitRange",[],"BUT")),ChanDotExp (ZVar ("t_sv_extendedTMPLimitRange",[],""))]) CSPSkip))))))))))))))))))) (CSPCommAction (ChanComm "connectDialyzer" []) (CSPCommAction (ChanComm "fillArterialDrip" []) (CSPCommAction (ChanComm "stopBP" []) CSPSkip)))) (CSPCommAction (ChanComm "initPhase" []) (CSPCommAction (ChanComm "connectThePatient" []) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_signalLamp",[],"BUT")),ChanDotExp (ZVar ("OFF",[],""))]) (CSPCommAction (ChanComm "connPatientArterially" []) (CSPCommAction (ChanComm "connPatientVenously" []) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_signalLamp",[],"BUT")),ChanDotExp (ZVar ("ON",[],""))]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_hdMode",[],"BUT")),ChanDotExp (ZVar ("ON",[],""))]) (CSPSeq (CSPInterleave (CSPInterleave (CSPInterleave (CSPInterleave CSPSkip (CSPCommAction (ChanComm "setMinUFRateTreat" [ChanInp "ON"]) CSPSkip)) CSPSkip) (CSPCommAction (ChanComm "setArtBolusVol" [ChanInp "t_sv_artBolusVol"]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_artBolusVol",[],"NAT")),ChanDotExp (ZVar ("t_sv_artBolusVol",[],""))]) CSPSkip))) (CSPCommAction (ChanComm "senHDMode" [ChanDotExp (ZVar ("OFF",[],""))]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_signalLamp",[],"BUT")),ChanDotExp (ZVar ("OFF",[],""))]) CSPSkip))) (CSPCommAction (ChanComm "endTreatment" []) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_signalLamp",[],"BUT")),ChanDotExp (ZVar ("OFF",[],""))]) CSPSkip))))))))))) (CSPCommAction (ChanComm "endPhase" []) CSPSkip)))))))))))))) (CSPCommAction (ChanComm "terminate" []) CSPSkip)) (CSPParAction "Memory" [ZVar ("b_NAT",[],""),ZVar ("b_BUT",[],"")])) (CSExpr "MEMI"))))))
Process (CProcess "SysClock" (ProcDef (ProcStalessMain [CParAction "Memory" (CircusAction (CActionCommand (CVResDecl [Choose ("b_NAT",[],"") (ZVar ("BINDING_NAT",[],""))] (CSPExtChoice (CSPExtChoice (CSPRepExtChoice [Choose ("n",[],"NAT") (ZCall (ZVar ("\\dom",[],"")) (ZVar ("b_NAT",[],"")))] (CSPCommAction (ChanComm "mget" [ChanDotExp (ZVar ("n",[],"NAT")),ChanOutExp (ZCall (ZVar ("b_NAT",[],"")) (ZVar ("n",[],"NAT")))]) (CSPParAction "Memory" [ZVar ("b_NAT",[],"")]))) (CSPRepExtChoice [Choose ("n",[],"NAT") (ZCall (ZVar ("\\dom",[],"")) (ZVar ("b_NAT",[],"")))] (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("n",[],"b_NAT")),ChanInpPred "nv" (ZMember (ZVar ("nv",[],"NAT")) (ZCall (ZVar ("\\delta",[],"")) (ZVar ("n",[],"NAT"))))]) (CSPParAction "Memory" [ZCall (ZVar ("\\oplus",[],"")) (ZTuple [ZVar ("b_NAT",[],""),ZSetDisplay [ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("n",[],""),ZVar ("nv",[],"")])]])])))) (CSPCommAction (ChanComm "terminate" []) CSPSkip))))),CParAction "MemoryMerge" (CircusAction (CActionCommand (CVResDecl [Choose ("b_NAT",[],"") (ZVar ("BINDING_NAT",[],"")),Choose ("ns",[],"") (ZCall (ZVar ("\\seq",[],"")) (ZVar ("NAME",[],"")))] (CSPExtChoice (CSPExtChoice (CSPRepExtChoice [Choose ("n",[],"NAT") (ZCall (ZVar ("\\dom",[],"")) (ZVar ("b_NAT",[],"")))] (CSPCommAction (ChanComm "lget" [ChanDotExp (ZVar ("n",[],"NAT")),ChanOutExp (ZCall (ZVar ("b_NAT",[],"")) (ZVar ("n",[],"NAT")))]) (CSPParAction "MemoryMerge" [ZVar ("b_NAT",[],""),ZVar ("ns",[],"")]))) (CSPRepExtChoice [Choose ("n",[],"NAT") (ZCall (ZVar ("\\dom",[],"")) (ZVar ("b_NAT",[],"")))] (CSPCommAction (ChanComm "lset" [ChanDotExp (ZVar ("n",[],"NAT")),ChanInpPred "nv" (ZMember (ZVar ("nv",[],"NAT")) (ZCall (ZVar ("\\delta",[],"")) (ZVar ("n",[],"NAT"))))]) (CSPParAction "MemoryMerge" [ZCall (ZVar ("\\oplus",[],"")) (ZTuple [ZVar ("b_NAT",[],""),ZSetDisplay [ZCall (ZVar ("\\mapsto",[],"")) (ZTuple [ZVar ("n",[],""),ZVar ("nv",[],"")])]]),ZVar ("ns",[],"")])))) (CSPCommAction (ChanComm "lterminate" []) (CSPRepSeq [Choose ("bd",[],"") (ZSeqDisplay [ZVar ("b_NAT",[],"")]),Choose ("n",[],"") (ZSeqDisplay [ZVar ("ns",[],"")])] (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("n",[],"")),ChanOutExp (ZCall (ZVar ("bd",[],"")) (ZVar ("n",[],"")))]) CSPSkip)))))))] (CSPRepIntChoice [Choose ("b_NAT",[],"") (ZVar ("BINDING_NAT",[],""))] (CSPHide (CSPNSParal [] (CSExpr "MEMI") [ZVar ("b_NAT",[],"")] (CSPSeq (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_time",[],"NAT")),ChanDotExp (ZInt 0)]) (CSPRecursion "X" (CSPSeq (CSPInterleave (CSPCommAction (ChanComm "tick" []) (CSPCommAction (ChanComm "mget" [ChanDotExp (ZVar ("sv_time",[],"NAT")),ChanInp "v_sv_time"]) (CSPCommAction (ChanComm "mset" [ChanDotExp (ZVar ("sv_time",[],"NAT")),ChanDotExp (ZCall (ZVar ("+",[],"")) (ZTuple [ZVar ("v_sv_time",[],"NAT"),ZInt 1]))]) CSPSkip))) (CSPCommAction (ChanComm "mget" [ChanDotExp (ZVar ("sv_time",[],"NAT")),ChanInp "v_sv_time"]) (CSPCommAction (ChanComm "getCurrentTime" [ChanDotExp (ZVar ("v_sv_time",[],"NAT"))]) CSPSkip))) (CActionName "X")))) (CSPCommAction (ChanComm "terminate" []) CSPSkip)) (CSPParAction "Memory" [ZVar ("b_NAT",[],"")])) (CSExpr "MEMI"))))))
