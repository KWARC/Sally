"use strict";
/** @suppress {duplicate}*/var sally;
if (typeof(sally)=="undefined") {sally = {};}

sally.Init = PROTO.Message("sally.Init",{
	options: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 1
	}});
sally.Document = PROTO.Message("sally.Document",{
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	Player: PROTO.Enum("sally.Document.Player",{
		MS_EXCELL :1,
		OO_CALC :2,
		Inventor :3	}),
	player: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.Document.Player;},
		id: 2
	}});
sally.ProjectProperties = PROTO.Message("sally.ProjectProperties",{
	ConfigurationFile: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	}});
sally.ConfigFile = PROTO.Message("sally.ConfigFile",{
	projectFiles: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.Document;},
		id: 1
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
sally.IdentificationData = PROTO.Message("sally.IdentificationData",{
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
	},
	parameters: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.Parameter;},
		id: 3
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
		type: function(){return PROTO.string;},
		id: 6
	}});
sally.Error = PROTO.Message("sally.Error",{
	ErrorType: PROTO.Enum("sally.Error.ErrorType",{
		GENERAL_ERROR :0,
		CANNOT_PARSE_MESSAGE :1,
		WRONG_PARAMS :2,
		WRONG_SENDER :3	}),
	code: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.Error.ErrorType;},
		id: 1
	},
	description: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 2
	}});
sally.SemanticMode = PROTO.Message("sally.SemanticMode",{
	SemMode: PROTO.Enum("sally.SemanticMode.SemMode",{
		DEFINITION_LOOKUP :0,
		SEMANTIC_NAVIGATION :1,
		SEMANTIC_MAPPING :2,
		SEMANTIC_VIEW :3,
		PROJECT_MODE :4	}),
	mode: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.SemanticMode.SemMode;},
		id: 1
	},
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	}});
sally.WhoAmI = PROTO.Message("sally.WhoAmI",{
	ClientType: PROTO.Enum("sally.WhoAmI.ClientType",{
		Alex :0,
		Theo :1,
		Admin :2	}),
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
sally.CADAlexClick = PROTO.Message("sally.CADAlexClick",{
	identificationData: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.IdentificationData;},
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
	key: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	}});
sally.CADKeyValue = PROTO.Message("sally.CADKeyValue",{
	key: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	value: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.IdentificationData;},
		id: 2
	}});
sally.CADSemanticData = PROTO.Message("sally.CADSemanticData",{
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	},
	map: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.CADKeyValue;},
		id: 2
	}});
sally.IdData = PROTO.Message("sally.IdData",{
	id: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 1
	}});
sally.IdList = PROTO.Message("sally.IdList",{
	ids: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.IdData;},
		id: 1
	}});
sally.StringData = PROTO.Message("sally.StringData",{
	name: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 1
	}});
sally.CellPosition = PROTO.Message("sally.CellPosition",{
	sheet: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
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
sally.NavigateTo = PROTO.Message("sally.NavigateTo",{
	sheet: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
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
sally.CellSpaceInformation = PROTO.Message("sally.CellSpaceInformation",{
	position: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.CellPosition;},
		id: 1
	},
	width: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 2
	},
	height: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 3
	}});
sally.CellPositions = PROTO.Message("sally.CellPositions",{
	cellPositions: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.CellSpaceInformation;},
		id: 1
	}});
sally.CellRange = PROTO.Message("sally.CellRange",{
	start: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.CellPosition;},
		id: 1
	},
	end: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.CellPosition;},
		id: 2
	}});
sally.CellRanges = PROTO.Message("sally.CellRanges",{
	range: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.CellRange;},
		id: 1
	}});
sally.CellData = PROTO.Message("sally.CellData",{
	position: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.CellSpaceInformation;},
		id: 1
	},
	value: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 2
	},
	formula: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 3
	}});
sally.RangeData = PROTO.Message("sally.RangeData",{
	cells: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.CellData;},
		id: 1
	}});
sally.BorderLine = PROTO.Message("sally.BorderLine",{
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
sally.CellBorder = PROTO.Message("sally.CellBorder",{
	top: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.BorderLine;},
		id: 1
	},
	bottom: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.BorderLine;},
		id: 2
	},
	left: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.BorderLine;},
		id: 3
	},
	right: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.BorderLine;},
		id: 4
	}});
sally.Font = PROTO.Message("sally.Font",{
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
sally.Cell = PROTO.Message("sally.Cell",{
	data: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.CellData;},
		id: 1
	},
	backColor: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 2
	},
	font: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.Font;},
		id: 3
	},
	border: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.CellBorder;},
		id: 4
	}});
sally.Sheet = PROTO.Message("sally.Sheet",{
	id: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 1
	},
	cells: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.Cell;},
		id: 2
	}});
sally.ParsingParameter = PROTO.Message("sally.ParsingParameter",{
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
sally.Data = PROTO.Message("sally.Data",{
	sheets: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.Sheet;},
		id: 1
	},
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 2
	},
	parameter: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.ParsingParameter;},
		id: 3
	}});
sally.DataParameter= PROTO.Enum("sally.DataParameter",{
		AllDiff :1,
		SameStringSameElement :2,
		SameContentSameElement :3});
sally.FBCreateData = PROTO.Message("sally.FBCreateData",{
	range: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.RangeData;},
		id: 1
	},
	legends: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.IdList;},
		id: 2
	},
	parameter: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.DataParameter;},
		id: 3
	},
	connectToAll: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.IdList;},
		id: 4
	}});
sally.LegendCreateData = PROTO.Message("sally.LegendCreateData",{
	items: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.RangeData;},
		id: 1
	},
	header: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.CellData;},
		id: 2
	},
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 3
	},
	parameter: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.DataParameter;},
		id: 4
	}});
sally.AbstractElementMsg = PROTO.Message("sally.AbstractElementMsg",{
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
	},
	formula: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 3
	},
	parameters: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return PROTO.int32;},
		id: 4
	}});
sally.AbstractDataModelMsg = PROTO.Message("sally.AbstractDataModelMsg",{
	elements: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.AbstractElementMsg;},
		id: 1
	}});
sally.LegendMsg = PROTO.Message("sally.LegendMsg",{
	id: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 1
	},
	items: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return PROTO.int32;},
		id: 2
	},
	header: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.int32;},
		id: 3
	}});
sally.LegendProductEntryMsg = PROTO.Message("sally.LegendProductEntryMsg",{
	legends: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return PROTO.int32;},
		id: 1
	},
	elements: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return PROTO.int32;},
		id: 2
	}});
sally.LegendProductMsg = PROTO.Message("sally.LegendProductMsg",{
	legends: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return PROTO.int32;},
		id: 1
	},
	entries: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.LegendProductEntryMsg;},
		id: 2
	}});
sally.FBEntryMsg = PROTO.Message("sally.FBEntryMsg",{
	domainElem: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.LegendProductEntryMsg;},
		id: 1
	},
	absElemId: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 2
	}});
sally.FunctionalBlockMsg = PROTO.Message("sally.FunctionalBlockMsg",{
	id: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 1
	},
	domain: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.LegendProductMsg;},
		id: 2
	},
	entry: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.FBEntryMsg;},
		id: 3
	}});
sally.AbstractSpreadsheetMsg = PROTO.Message("sally.AbstractSpreadsheetMsg",{
	elements: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.AbstractDataModelMsg;},
		id: 1
	},
	legends: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.LegendMsg;},
		id: 2
	},
	functionalBlocks: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.FunctionalBlockMsg;},
		id: 3
	}});
sally.CellSpaceInformationMsg = PROTO.Message("sally.CellSpaceInformationMsg",{
	worksheet: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
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
	}});
sally.ElementMappingMsg = PROTO.Message("sally.ElementMappingMsg",{
	position: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.CellSpaceInformation;},
		id: 1
	},
	absElemId: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 2
	}});
sally.LegendMappingMsg = PROTO.Message("sally.LegendMappingMsg",{
	elementPositions: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.ElementMappingMsg;},
		id: 1
	},
	headerPosition: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.CellSpaceInformation;},
		id: 2
	},
	headerElementId: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.int32;},
		id: 3
	},
	legendId: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 4
	}});
sally.DomainMappingMsg = PROTO.Message("sally.DomainMappingMsg",{
	position: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.CellSpaceInformation;},
		id: 1
	},
	domainElement: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.LegendProductEntryMsg;},
		id: 2
	}});
sally.FunctionalBlockMappingMsg = PROTO.Message("sally.FunctionalBlockMappingMsg",{
	domain: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.LegendProductMsg;},
		id: 1
	},
	elementMapping: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.ElementMappingMsg;},
		id: 2
	},
	domainMapping: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.DomainMappingMsg;},
		id: 3
	},
	fbId: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 4
	}});
sally.MappingMsg = PROTO.Message("sally.MappingMsg",{
	legendMappings: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.LegendMappingMsg;},
		id: 1
	},
	fbMappings: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.FunctionalBlockMappingMsg;},
		id: 2
	}});
sally.ModelDataMsg = PROTO.Message("sally.ModelDataMsg",{
	asm: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.AbstractSpreadsheetMsg;},
		id: 1
	},
	mapping: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.MappingMsg;},
		id: 2
	}});
sally.AreaInformationMsg = PROTO.Message("sally.AreaInformationMsg",{
	TypeEnum: PROTO.Enum("sally.AreaInformationMsg.TypeEnum",{
		LEGEND :0,
		LEGENDHEADER :1,
		FB :3	}),
	id: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 1
	},
	type: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.AreaInformationMsg.TypeEnum;},
		id: 2
	},
	ranges: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.CellRanges;},
		id: 3
	}});
sally.AmbiguousInformationMsg = PROTO.Message("sally.AmbiguousInformationMsg",{
	position: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.CellPosition;},
		id: 1
	},
	relatedAreaIds: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return PROTO.int32;},
		id: 2
	}});
sally.AffiliationInformationMsg = PROTO.Message("sally.AffiliationInformationMsg",{
	id: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.int32;},
		id: 1
	},
	affiliatedIds: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return PROTO.int32;},
		id: 2
	}});
sally.ParsingResultMsg = PROTO.Message("sally.ParsingResultMsg",{
	areas: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.AreaInformationMsg;},
		id: 1
	},
	ambig: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.AmbiguousInformationMsg;},
		id: 2
	},
	affiliation: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.AffiliationInformationMsg;},
		id: 3
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
sally.SemanticData = PROTO.Message("sally.SemanticData",{
	data: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return PROTO.string;},
		id: 1
	},
	projectConfig: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.ProjectProperties;},
		id: 2
	},
	absSpreadsheet: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.ModelDataMsg;},
		id: 3
	},
	fileName: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 4
	}});
sally.SpreadsheetModel = PROTO.Message("sally.SpreadsheetModel",{
	asm: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.ModelDataMsg;},
		id: 1
	},
	ontomapping: {
		options: {},
		multiplicity: PROTO.repeated,
		type: function(){return sally.SpreadsheetOntologyPair;},
		id: 2
	}});
sally.SpreadsheetOntologyPair = PROTO.Message("sally.SpreadsheetOntologyPair",{
	asmid: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return sally.IdData;},
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
sally.ContainerMessage = PROTO.Message("sally.ContainerMessage",{
	type: {
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
	},
	callback: {
		options: {},
		multiplicity: PROTO.required,
		type: function(){return PROTO.string;},
		id: 3
	},
	sally_Frame: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.Frame;},
		id: 7
	},
	sally_FormulaInfo: {
		options: {},
		multiplicity: PROTO.optional,
		type: function(){return sally.FormulaInfo;},
		id: 10
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
