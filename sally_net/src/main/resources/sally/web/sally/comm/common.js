"use strict";
/** @suppress {duplicate}*/var Sally;
if (typeof(Sally)=="undefined") {Sally = {};}

Sally.Cookie = PROTO.Message("Sally.Cookie",{
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
Sally.SwitchToApp = PROTO.Message("Sally.SwitchToApp",{
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	}});
Sally.TheoOpenWindow = PROTO.Message("Sally.TheoOpenWindow",{
	position: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return Sally.ScreenCoordinates;},
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
		type: function(){return Sally.Cookie;},
		id: 6
	}});
Sally.TheoChangeWindow = PROTO.Message("Sally.TheoChangeWindow",{
	position: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return Sally.ScreenCoordinates;},
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
		type: function(){return Sally.Cookie;},
		id: 6
	},
	windowid: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 7
	}});
Sally.TheoCloseWindow = PROTO.Message("Sally.TheoCloseWindow",{
	windowid: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 1
	}});
Sally.WhoAmI = PROTO.Message("Sally.WhoAmI",{
	ClientType: PROTO.Enum("Sally.WhoAmI.ClientType",{
		Alex :0,
		Theo :1	}),
	EnvironmentType: PROTO.Enum("Sally.WhoAmI.EnvironmentType",{
		Desktop :0,
		Web :1	}),
	clientType: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return Sally.WhoAmI.ClientType;},
		id: 1
	},
	environmentType: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return Sally.WhoAmI.EnvironmentType;},
		id: 2
	},
	interfaces: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return PROTO.string;},
		id: 4
	},
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 5
	}});
Sally.AlexData = PROTO.Message("Sally.AlexData",{
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
	},
	shareJSColection: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 3
	},
	shareJSDocument: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 4
	}});
Sally.SallyFrame = PROTO.Message("Sally.SallyFrame",{
	fileName: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 1
	}});
Sally.SallyFrameChoice = PROTO.Message("Sally.SallyFrameChoice",{
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
Sally.SallyFrameService = PROTO.Message("Sally.SallyFrameService",{
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
Sally.SallyFrameResponse = PROTO.Message("Sally.SallyFrameResponse",{
	frameName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	frameServices: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return Sally.SallyFrameService;},
		id: 2
	}});
Sally.SallyFrameList = PROTO.Message("Sally.SallyFrameList",{
	frames: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return Sally.SallyFrameResponse;},
		id: 1
	},
	callbackToken: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.int64;},
		id: 2
	},
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 3
	}});
Sally.ScreenCoordinates = PROTO.Message("Sally.ScreenCoordinates",{
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
Sally.Parameter = PROTO.Message("Sally.Parameter",{
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
Sally.RangeSelection = PROTO.Message("Sally.RangeSelection",{
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
Sally.AlexRangeRequest = PROTO.Message("Sally.AlexRangeRequest",{
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	selection: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return Sally.RangeSelection;},
		id: 2
	}});
Sally.AlexClick = PROTO.Message("Sally.AlexClick",{
	Sheet: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	range: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return Sally.RangeSelection;},
		id: 2
	},
	position: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return Sally.ScreenCoordinates;},
		id: 3
	},
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 4
	}});
Sally.StartSubTask = PROTO.Message("Sally.StartSubTask",{
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
Sally.CADAlexClick = PROTO.Message("Sally.CADAlexClick",{
	cadNodeId: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	position: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return Sally.ScreenCoordinates;},
		id: 2
	},
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 3
	}});
Sally.CADNavigateTo = PROTO.Message("Sally.CADNavigateTo",{
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
Sally.CADNode = PROTO.Message("Sally.CADNode",{
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
		type: function(){return Sally.CADNode;},
		id: 3
	},
	parameters: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return Sally.Parameter;},
		id: 4
	}});
Sally.CADSemanticData = PROTO.Message("Sally.CADSemanticData",{
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	root_node: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return Sally.CADNode;},
		id: 2
	}});
Sally.SpreadsheetAlexData = PROTO.Message("Sally.SpreadsheetAlexData",{
	asm: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return Sally.ModelDataMsg;},
		id: 2
	}});
Sally.SoftwareObject = PROTO.Message("Sally.SoftwareObject",{
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	uri: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	}});
Sally.MMTUri = PROTO.Message("Sally.MMTUri",{
	uri: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	}});
Sally.BlockInfo = PROTO.Message("Sally.BlockInfo",{
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
Sally.SpreadsheetDocMeta = PROTO.Message("Sally.SpreadsheetDocMeta",{
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
Sally.GetSheets = PROTO.Message("Sally.GetSheets",{
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
Sally.GetBlocks = PROTO.Message("Sally.GetBlocks",{
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
Sally.BlockList = PROTO.Message("Sally.BlockList",{
	blocks: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return Sally.BlockInfo;},
		id: 1
	}});
Sally.CreateBlock = PROTO.Message("Sally.CreateBlock",{
	blockInfo: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return Sally.BlockInfo;},
		id: 1
	},
	callbackToken: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.int64;},
		id: 2
	}});
Sally.BuilderMsg = PROTO.Message("Sally.BuilderMsg",{
	Type: PROTO.Enum("Sally.BuilderMsg.Type",{
		MathML :1,
		OpenMath :2	}),
	type: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return Sally.BuilderMsg.Type;},
		id: 1
	}});
Sally.ValueInterpretationMsg = PROTO.Message("Sally.ValueInterpretationMsg",{
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
		type: function(){return Sally.BuilderMsg;},
		id: 3
	}});
Sally.CellSpaceInformationMsg = PROTO.Message("Sally.CellSpaceInformationMsg",{
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
Sally.Property = PROTO.Message("Sally.Property",{
	propertyID: {
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
Sally.BlockMsg = PROTO.Message("Sally.BlockMsg",{
	Type: PROTO.Enum("Sally.BlockMsg.Type",{
		Atomic :1,
		Composed :2	}),
	type: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return Sally.BlockMsg.Type;},
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
		type: function(){return Sally.ValueInterpretationMsg;},
		id: 4
	},
	properties: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return Sally.Property;},
		id: 5
	},
	position: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return Sally.CellSpaceInformationMsg;},
		id: 6
	},
	subBlockIds: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return PROTO.int32;},
		id: 7
	}});
Sally.CellTupleMsg = PROTO.Message("Sally.CellTupleMsg",{
	tuple: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return Sally.CellSpaceInformationMsg;},
		id: 1
	}});
Sally.CellDependencyDescriptionMsg = PROTO.Message("Sally.CellDependencyDescriptionMsg",{
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
Sally.RelationMsg = PROTO.Message("Sally.RelationMsg",{
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
		type: function(){return Sally.CellTupleMsg;},
		id: 5
	},
	cellDependencyDescriptions: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return Sally.CellDependencyDescriptionMsg;},
		id: 6
	}});
Sally.ModelDataMsg = PROTO.Message("Sally.ModelDataMsg",{
	blocks: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return Sally.BlockMsg;},
		id: 1
	},
	relations: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return Sally.RelationMsg;},
		id: 2
	}});
Sally.SketchSelect = PROTO.Message("Sally.SketchSelect",{
	id: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
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
		type: function(){return Sally.ScreenCoordinates;},
		id: 3
	}});
Sally.SketchAtomic = PROTO.Message("Sally.SketchAtomic",{
	id: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	mmturi: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return Sally.MMTUri;},
		id: 2
	}});
Sally.SketchRelation = PROTO.Message("Sally.SketchRelation",{
	parts: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return PROTO.string;},
		id: 1
	},
	relation: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return Sally.MMTUri;},
		id: 2
	}});
Sally.SketchASM = PROTO.Message("Sally.SketchASM",{
	parts: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return Sally.SketchAtomic;},
		id: 1
	},
	relations: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return Sally.SketchRelation;},
		id: 2
	},
	sketchTitle: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 3
	}});
Sally.SketchSelectPart = PROTO.Message("Sally.SketchSelectPart",{
	id: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	}});
Sally.HTMLSelect = PROTO.Message("Sally.HTMLSelect",{
	id: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
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
		type: function(){return Sally.ScreenCoordinates;},
		id: 3
	}});
Sally.HTMLAtomic = PROTO.Message("Sally.HTMLAtomic",{
	id: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	mmturi: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return Sally.MMTUri;},
		id: 2
	}});
Sally.HTMLASM = PROTO.Message("Sally.HTMLASM",{
	parts: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return Sally.HTMLAtomic;},
		id: 1
	}});
Sally.HTMLSelectPart = PROTO.Message("Sally.HTMLSelectPart",{
	id: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	}});
