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
		CAD :2,
		Sketch :3	}),
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
sally.SallyFrameChoice = PROTO.Message("sally.SallyFrameChoice",{
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	choiceId: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 2
	},
	callbackToken: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int64;},
		id: 3
	}});
sally.SallyFrameService = PROTO.Message("sally.SallyFrameService",{
	id: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 1
	},
	name: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	},
	description: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 3
	}});
sally.SallyFrameResponse = PROTO.Message("sally.SallyFrameResponse",{
	frameName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	frameServices: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.SallyFrameService;},
		id: 2
	}});
sally.SallyFrameList = PROTO.Message("sally.SallyFrameList",{
	frames: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.SallyFrameResponse;},
		id: 1
	},
	callbackToken: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.int64;},
		id: 2
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
	},
	callbackToken: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.int64;},
		id: 2
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
sally.SpreadsheetAlexData = PROTO.Message("sally.SpreadsheetAlexData",{
	asm: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.ModelDataMsg;},
		id: 2
	}});
sally.MMTUri = PROTO.Message("sally.MMTUri",{
	uri: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	}});
sally.BlockInfo = PROTO.Message("sally.BlockInfo",{
	name: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 1
	},
	range: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 2
	},
	meaning: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 3
	},
	order: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.int32;},
		id: 4
	},
	id: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.int32;},
		id: 5
	}});
sally.SpreadsheetDocMeta = PROTO.Message("sally.SpreadsheetDocMeta",{
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	sheets: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return PROTO.string;},
		id: 2
	}});
sally.GetMeta = PROTO.Message("sally.GetMeta",{
	fileName: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 1
	},
	callbackToken: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.int64;},
		id: 2
	}});
sally.GetBlocks = PROTO.Message("sally.GetBlocks",{
	fileName: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 1
	},
	sheet: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 2
	},
	callbackToken: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.int64;},
		id: 3
	}});
sally.BlockList = PROTO.Message("sally.BlockList",{
	blocks: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.BlockInfo;},
		id: 1
	}});
sally.CreateBlock = PROTO.Message("sally.CreateBlock",{
	blockInfo: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.BlockInfo;},
		id: 1
	},
	callbackToken: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.int64;},
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
sally.SketchSelect = PROTO.Message("sally.SketchSelect",{
	id: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 1
	},
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	},
	position: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.ScreenCoordinates;},
		id: 3
	}});
sally.SketchAtomic = PROTO.Message("sally.SketchAtomic",{
	id: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 1
	},
	mmturi: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.MMTUri;},
		id: 2
	}});
sally.SketchRelation = PROTO.Message("sally.SketchRelation",{
	parts: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return PROTO.int32;},
		id: 1
	},
	relation: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.MMTUri;},
		id: 2
	}});
sally.SketchASM = PROTO.Message("sally.SketchASM",{
	parts: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.SketchAtomic;},
		id: 1
	},
	relations: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.SketchRelation;},
		id: 2
	}});
