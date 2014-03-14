(function() {

	function getAllRecords(callback) {
		var getBlocks = new sally.GetBlocks();
		Communication.sendMessage(getBlocks, function(data) {
			var result = [];
			for (var blkidx=0; blkidx < data.blocks.length; blkidx++) {
				var block = data.blocks[blkidx];
				result.push({
					name : block.name,
					meaning : block.meaning,
					id : block.id,
					range : block.range
				});
			}
			console.log(result);
			callback(result, "ok");
		});
	}
	
	function addRecord(data, callback) {
		var block = new sally.BlockInfo();
		block.name = data["name"];
		block.range = data["range"];
		block.meaning = data["meaning"];
		block.order = data["order"];

		var cmd = new sally.CreateBlock();
		cmd.blockInfo = block;
		
		Communication.sendMessage(cmd, function(data) {
			//model.id = data.id;
		});
	}
	
	Backbone.ajax = function(request) {
		if (request.type == "GET") {
			getAllRecords(request.success);
		}
		
		if (request.type == "PUT") {
			addRecord(JSON.parse(request.data), request.success);
		}
	}
	
})();

