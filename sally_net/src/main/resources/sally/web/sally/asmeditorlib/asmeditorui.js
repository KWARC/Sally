 function render_blocks(root, blocks) {
	var headers = ["Meaning" , "Name", "Range", "Options"];

	var header_elem = $("<tr>");

	for (var head in headers) {
		header_elem.append($("<th>").text(headers[head]));
	}

	var blocks_elem = [];
	for (var block in blocks) {
		var block_elem = $("<tr>");
		var block_info = blocks[block];
		for (var head in headers) {
			var hd = headers[head].toLowerCase();
			block_elem.append($("<td>").text(block_info[hd]));
		}
		blocks_elem.push(block_elem);
	}
	
	var new_elem = $("<tr>")
		.append($("<td>").append(
				$("<input>").addClass("span7"),
				$("<button>").addClass("btn").text("browse").click(function() {
					var workflow = new sally.StartSubTask();
					workflow.workflowID = "Sally.browse_ontology";
					Communication.sendMessage(workflow, function() {
						app.log("haha got something back");
					});
				}))
		)
		.append($("<td>").append($("<input>").addClass("span12")))

		.append($("<td>").append(
				$("<input>").addClass("span5"),
				$("<span>").text(":"),
				$("<input>").addClass("span5"))
			)
		.append($("<td>").append($("<button>").addClass("btn").text("add")));
	
	$(root).append($("<table>").addClass("table").append(
			header_elem,
			blocks_elem,
			new_elem
	));
}

function open_spread(spreadsheet) {
	console.log("opening spread");

}

function open_sheet(spreadsheet, sheet) {
	$("#block-page").empty();
	render_blocks($("#block-page"), asmeditor.getBlocks(spreadsheet, sheet));
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