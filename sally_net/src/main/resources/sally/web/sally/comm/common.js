"use strict";
/** @suppress {duplicate}*/var sally;
if (typeof(sally)=="undefined") {sally = {};}

sally.Cookie = PROTO.Message("sally.Cookie",{
	url: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	cookie: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	}});
sally.SwitchToApp = PROTO.Message("sally.SwitchToApp",{
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	}});
sally.TheoOpenWindow = PROTO.Message("sally.TheoOpenWindow",{
	position: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.ScreenCoordinates;},
		id: 1
	},
	url: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	},
	sizeX: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.int32;},
		id: 3
	},
	sizeY: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.int32;},
		id: 4
	},
	title: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 5
	},
	cookie: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.Cookie;},
		id: 6
	}});
sally.TheoChangeWindow = PROTO.Message("sally.TheoChangeWindow",{
	position: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.ScreenCoordinates;},
		id: 1
	},
	url: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 2
	},
	sizeX: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.int32;},
		id: 3
	},
	sizeY: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.int32;},
		id: 4
	},
	title: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 5
	},
	cookie: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.Cookie;},
		id: 6
	},
	windowid: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 7
	}});
sally.TheoCloseWindow = PROTO.Message("sally.TheoCloseWindow",{
	windowid: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 1
	}});
sally.WhoAmI = PROTO.Message("sally.WhoAmI",{
	ClientType: PROTO.Enum("sally.WhoAmI.ClientType",{
		Alex :0,
		Theo :1	}),
	EnvironmentType: PROTO.Enum("sally.WhoAmI.EnvironmentType",{
		Desktop :0,
		Web :1	}),
	DocType: PROTO.Enum("sally.WhoAmI.DocType",{
		Spreadsheet :0,
		Text :1,
		CAD :2	}),
	clientType: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.WhoAmI.ClientType;},
		id: 1
	},
	environmentType: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.WhoAmI.EnvironmentType;},
		id: 2
	},
	documentType: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.WhoAmI.DocType;},
		id: 3
	}});
sally.AlexData = PROTO.Message("sally.AlexData",{
	fileName: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 1
	},
	data: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 2
	}});
sally.SallyFrame = PROTO.Message("sally.SallyFrame",{
	fileName: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 1
	}});
sally.Init = PROTO.Message("sally.Init",{
	options: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 1
	}});
sally.ScreenCoordinates = PROTO.Message("sally.ScreenCoordinates",{
	x: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 1
	},
	y: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 2
	}});
sally.Parameter = PROTO.Message("sally.Parameter",{
	key: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	value: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	}});
sally.RangeSelection = PROTO.Message("sally.RangeSelection",{
	startRow: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 1
	},
	startCol: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 2
	},
	endRow: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 3
	},
	endCol: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 4
	},
	sheet: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 5
	}});
sally.AlexRangeRequest = PROTO.Message("sally.AlexRangeRequest",{
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	selection: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.RangeSelection;},
		id: 2
	}});
sally.AlexClick = PROTO.Message("sally.AlexClick",{
	Sheet: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	range: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.RangeSelection;},
		id: 2
	},
	position: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.ScreenCoordinates;},
		id: 3
	},
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 4
	}});
sally.StartSubTask = PROTO.Message("sally.StartSubTask",{
	workflowID: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	}});
sally.CADAlexClick = PROTO.Message("sally.CADAlexClick",{
	cadNodeId: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	position: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.ScreenCoordinates;},
		id: 2
	},
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 3
	}});
sally.CADNavigateTo = PROTO.Message("sally.CADNavigateTo",{
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	cadNodeId: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	}});
sally.CADNode = PROTO.Message("sally.CADNode",{
	id: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	im_uri: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 2
	},
	children: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.CADNode;},
		id: 3
	},
	parameters: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.Parameter;},
		id: 4
	}});
sally.CADSemanticData = PROTO.Message("sally.CADSemanticData",{
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	root_node: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.CADNode;},
		id: 2
	}});
sally.SemanticActionData = PROTO.Message("sally.SemanticActionData",{
	cd: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 1
	},
	name: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 2
	},
	fileName: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 3
	},
	senderId: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 4
	},
	sheetName: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 5
	},
	row: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.uint32;},
		id: 6
	},
	col: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.uint32;},
		id: 7
	},
	coordinates: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.ScreenCoordinates;},
		id: 8
	}});
sally.SpreadsheetAlexData = PROTO.Message("sally.SpreadsheetAlexData",{
	asm: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.ModelDataMsg;},
		id: 2
	}});
sally.SpreadsheetOntologyPair = PROTO.Message("sally.SpreadsheetOntologyPair",{
	asmid: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 1
	},
	uri: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	}});
sally.MMTUri = PROTO.Message("sally.MMTUri",{
	uri: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	}});
sally.OntologyData = PROTO.Message("sally.OntologyData",{
	concepts: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.OntologyConcept;},
		id: 1
	},
	relations: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.OntologyRelation;},
		id: 2
	}});
sally.OntologyConcept = PROTO.Message("sally.OntologyConcept",{
	uri: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	params: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return PROTO.string;},
		id: 2
	}});
sally.OntologyRelation = PROTO.Message("sally.OntologyRelation",{
	uri: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	srcConcept: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	},
	destConcept: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 3
	}});
sally.StringMap = PROTO.Message("sally.StringMap",{
	key: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	value: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	}});
sally.KnowledgeObject = PROTO.Message("sally.KnowledgeObject",{
	uri: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	values: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.StringMap;},
		id: 2
	}});
sally.KnowledgeBase = PROTO.Message("sally.KnowledgeBase",{
	objects: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.KnowledgeObject;},
		id: 1
	},
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	}});
sally.OntologyItem = PROTO.Message("sally.OntologyItem",{
	theory: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	symbol: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	}});
sally.ResourceContext = PROTO.Message("sally.ResourceContext",{
	actionId: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	}});
sally.ContextKnowledge = PROTO.Message("sally.ContextKnowledge",{
	context: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.OntologyItem;},
		id: 1
	}});
sally.FormulaRequest = PROTO.Message("sally.FormulaRequest",{
	actionId: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	}});
sally.FormulaInfo = PROTO.Message("sally.FormulaInfo",{
	json: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	}});
sally.TheoNavigateTo = PROTO.Message("sally.TheoNavigateTo",{
	term: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.OntologyItem;},
		id: 1
	},
	actionId: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	}});
sally.Frame = PROTO.Message("sally.Frame",{
	uid: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	actionId: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	}});
sally.ServiceCall = PROTO.Message("sally.ServiceCall",{
	uid: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	}});
sally.FormulaCell = PROTO.Message("sally.FormulaCell",{
	row: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 3
	},
	col: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 4
	},
	formula: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	value: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	}});
sally.FormulaSheetData = PROTO.Message("sally.FormulaSheetData",{
	sheetname: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	startRow: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 3
	},
	startCol: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 4
	},
	endRow: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 5
	},
	endCol: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 6
	},
	cellinf: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.FormulaCell;},
		id: 2
	}});
sally.FormulaMap = PROTO.Message("sally.FormulaMap",{
	filename: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	sheets: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.FormulaSheetData;},
		id: 2
	}});
sally.RequestASM = PROTO.Message("sally.RequestASM",{
	filename: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	}});
sally.SaveASM = PROTO.Message("sally.SaveASM",{
	semanticData: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	}});
sally.FileRef = PROTO.Message("sally.FileRef",{
	resourceURI: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	mime: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	}});
sally.FileContents = PROTO.Message("sally.FileContents",{
	file: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.FileRef;},
		id: 1
	},
	contents: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	}});
sally.TextPosition = PROTO.Message("sally.TextPosition",{
	line: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 1
	},
	col: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 2
	}});
sally.XMLPosition = PROTO.Message("sally.XMLPosition",{
	xpath: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	}});
sally.XMLNotification = PROTO.Message("sally.XMLNotification",{
	pos: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.XMLPosition;},
		id: 1
	},
	msg: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	},
	uri: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 3
	}});
sally.TextNotification = PROTO.Message("sally.TextNotification",{
	pos: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.TextPosition;},
		id: 1
	},
	msg: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	},
	uri: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 3
	}});
sally.TextFileNotifications = PROTO.Message("sally.TextFileNotifications",{
	file: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.FileRef;},
		id: 1
	},
	notifications: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.TextNotification;},
		id: 2
	}});
sally.TextAutocomplete = PROTO.Message("sally.TextAutocomplete",{
	file: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.FileRef;},
		id: 1
	},
	offset: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 2
	},
	fileContents: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 3
	}});
sally.CellPosition2 = PROTO.Message("sally.CellPosition2",{
	sheet: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	row: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 2
	},
	col: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 3
	}});
sally.CellPositions2 = PROTO.Message("sally.CellPositions2",{
	cellPositions: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.CellPosition2;},
		id: 1
	}});
sally.CellPositionsList2 = PROTO.Message("sally.CellPositionsList2",{
	cellPositionsList: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.CellPositions2;},
		id: 1
	}});
sally.CellRangePosition2 = PROTO.Message("sally.CellRangePosition2",{
	startPos: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.CellPosition2;},
		id: 1
	},
	endPos: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.CellPosition2;},
		id: 2
	}});
sally.StringMessage = PROTO.Message("sally.StringMessage",{
	data: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	}});
sally.IDMessage = PROTO.Message("sally.IDMessage",{
	id: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 1
	}});
sally.IDList = PROTO.Message("sally.IDList",{
	ids: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return PROTO.int32;},
		id: 1
	}});
sally.IntegerStringPair = PROTO.Message("sally.IntegerStringPair",{
	id: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 1
	},
	value: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	}});
sally.IntegerStringMapping = PROTO.Message("sally.IntegerStringMapping",{
	pair: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.IntegerStringPair;},
		id: 1
	}});
sally.BorderLine2 = PROTO.Message("sally.BorderLine2",{
	borderColor: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int64;},
		id: 1
	},
	formatStyle: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 2
	},
	excelBorderStyle: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.int32;},
		id: 3
	},
	excelBorderWeight: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.int32;},
		id: 4
	},
	ooInnerLineWidth: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.int32;},
		id: 5
	},
	ooOuterLineWidth: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.int32;},
		id: 6
	},
	ooLineDistance: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.int32;},
		id: 7
	}});
sally.CellBorder2 = PROTO.Message("sally.CellBorder2",{
	top: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.BorderLine2;},
		id: 1
	},
	bottom: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.BorderLine2;},
		id: 2
	},
	left: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.BorderLine2;},
		id: 3
	},
	right: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.BorderLine2;},
		id: 4
	}});
sally.Font2 = PROTO.Message("sally.Font2",{
	fontName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	fontColor: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 2
	},
	fontSize: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.Float;},
		id: 3
	},
	isItalic: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.bool;},
		id: 4
	},
	isBold: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.bool;},
		id: 5
	},
	isUnderlined: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.bool;},
		id: 6
	}});
sally.CellSize2 = PROTO.Message("sally.CellSize2",{
	cellHeight: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 1
	},
	cellWidth: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 2
	}});
sally.LayoutInformation2 = PROTO.Message("sally.LayoutInformation2",{
	backColor: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 1
	},
	border: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.CellBorder2;},
		id: 2
	},
	font: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.Font2;},
		id: 3
	},
	cellSize: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.CellSize2;},
		id: 4
	}});
sally.CellData2 = PROTO.Message("sally.CellData2",{
	position: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.CellPosition2;},
		id: 1
	},
	formula: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	},
	value: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 3
	},
	layout: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.LayoutInformation2;},
		id: 4
	}});
sally.SheetData2 = PROTO.Message("sally.SheetData2",{
	range: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.CellRangePosition2;},
		id: 1
	},
	cellData: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.CellData2;},
		id: 2
	}});
sally.DocumentData2 = PROTO.Message("sally.DocumentData2",{
	filename: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	sheets: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.SheetData2;},
		id: 2
	}});
sally.ParsingParameter2 = PROTO.Message("sally.ParsingParameter2",{
	useTextAsLegend: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.bool;},
		id: 1
	},
	useColorAsStructure: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.bool;},
		id: 2
	},
	useBorderAsStructure: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.bool;},
		id: 3
	},
	useFontAsStructure: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.bool;},
		id: 4
	}});
sally.ParsingMessage2 = PROTO.Message("sally.ParsingMessage2",{
	document: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.DocumentData2;},
		id: 1
	},
	parameter: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.ParsingParameter2;},
		id: 2
	}});
sally.BuilderMsg = PROTO.Message("sally.BuilderMsg",{
	Type: PROTO.Enum("sally.BuilderMsg.Type",{
		MathML :1,
		OpenMath :2	}),
	type: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.BuilderMsg.Type;},
		id: 1
	}});
sally.ValueInterpretationMsg = PROTO.Message("sally.ValueInterpretationMsg",{
	pattern: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	interpretationTemplate: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	},
	builderML: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.BuilderMsg;},
		id: 3
	}});
sally.CellSpaceInformationMsg = PROTO.Message("sally.CellSpaceInformationMsg",{
	worksheet: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	row: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 2
	},
	column: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 3
	},
	height: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.int32;},
		id: 4
	},
	width: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.int32;},
		id: 5
	}});
sally.BlockMsg = PROTO.Message("sally.BlockMsg",{
	Type: PROTO.Enum("sally.BlockMsg.Type",{
		Atomic :1,
		Composed :2	}),
	type: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.BlockMsg.Type;},
		id: 1
	},
	id: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 2
	},
	worksheet: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 3
	},
	valueInterpretations: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.ValueInterpretationMsg;},
		id: 4
	},
	position: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.CellSpaceInformationMsg;},
		id: 5
	},
	subBlockIds: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return PROTO.int32;},
		id: 6
	}});
sally.CellTupleMsg = PROTO.Message("sally.CellTupleMsg",{
	tuple: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.CellSpaceInformationMsg;},
		id: 1
	}});
sally.CellDependencyDescriptionMsg = PROTO.Message("sally.CellDependencyDescriptionMsg",{
	minX: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 1
	},
	maxX: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 2
	},
	minY: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 3
	},
	maxY: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 4
	},
	cellRelation: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 5
	}});
sally.RelationMsg = PROTO.Message("sally.RelationMsg",{
	id: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 1
	},
	relationType: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 2
	},
	uri: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 3
	},
	blockIDs: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return PROTO.int32;},
		id: 4
	},
	cellRelations: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.CellTupleMsg;},
		id: 5
	},
	cellDependencyDescriptions: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.CellDependencyDescriptionMsg;},
		id: 6
	}});
sally.ModelDataMsg = PROTO.Message("sally.ModelDataMsg",{
	blocks: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.BlockMsg;},
		id: 1
	},
	relations: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.RelationMsg;},
		id: 2
	}});
