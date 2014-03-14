
function open_spread(spreadsheet) {
	console.log("opening spread");

}

function open_sheet(spreadsheet, sheet) {
	$("#block-page").empty();
}

function refresh_tree() {
	// var cmd = new sally.GetSheets();
	var sheet_tree = null;
	
	Communication.sendMessage(cmd, function(data) {
		var sheets = [];
		$.each(data.sheets, function(idx, stName) {
			sheets.push($("<li>").append(
					$("<span>")
					.append(	$("<i>").addClass("icon-sheet"))
					.append($("<a>").text(stName).click(function() {
						open_sheet(name, stName);
					}))
			));
		});
		sheet_tree = $("<li>").append(
				$("<span>")
				.append(	$("<i>").addClass("icon-xls"))
				.append($("<a>").text(data.fileName).click(function() {
					open_spread(name);
				})))
				.append($("<ul>").append(sheets));
		$("#block-spread-root").append(sheet_tree); 		
	});
}