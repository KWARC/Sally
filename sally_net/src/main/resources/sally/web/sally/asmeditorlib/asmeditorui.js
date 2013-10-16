
function open_spread(spreadsheet) {
	console.log("opening spread");

}

function open_sheet(spreadsheet, sheet) {
	$("#block-page").empty();
}

function refresh_tree() {
	var sheet_tree = [];
	$.each(asmeditor.getSpreadsheets(), function(idx, name) {
		var sheets = [];
		$.each(asmeditor.getSheets(name), function(idx, stName) {
			sheets.push($("<li>").append(
					$("<span>")
					.append(	$("<i>").addClass("icon-sheet"))
					.append($("<a>").text(stName).click(function() {
						open_sheet(name, stName);
					}))
			));
		});
		sheet_tree.push($("<li>").append(
				$("<span>")
				.append(	$("<i>").addClass("icon-xls"))
				.append($("<a>").text(name).click(function() {
					open_spread(name);
				})))
				.append($("<ul>").append(sheets))
		);
	});
	$("#block-spread-root").append(sheet_tree);
}