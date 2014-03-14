/**
 * Backbone localStorage Adapter
 * Version 1.1.0
 *
 * https://github.com/jeromegn/Backbone.localStorage
 */
(function (root, factory) {
	if (typeof define === "function" && define.amd) {
		// AMD. Register as an anonymous module.
		define(["underscore","backbone"], function(_, Backbone) {
			// Use global variables if the locals are undefined.
			return factory(_ || root._, Backbone || root.Backbone);
		});
	} else {
		// RequireJS isn't being used. Assume underscore and backbone are loaded in <script> tags
		factory(_, Backbone);
	}
}(this, function(_, Backbone) {

	Backbone.LocalStorage = window.Store = function(name) {
		this.name = name;
		var store = {};
		this.records = [];
	};

	_.extend(Backbone.LocalStorage.prototype, {
		
		findAll: function() {
			console.log("finding all");
		},
		
		update: function(model) {
			
		},

		create: function(model) {
			console.log("creating "+model);
			var block = new sally.BlockInfo();
			block.name = model.get("name");
			block.range = model.get("range");
			block.meaning = model.get("meaning");
			block.order = model.get("order");

			var cmd = new sally.CreateBlock();
			cmd.blockInfo = block;
			
			console.log("sending");
			Communication.sendMessage(cmd, function(data) {
				console.log("blockid = "+data.id);
				model.id = data.id;
			});
		}
	});;

	Backbone.LocalStorage.sync = function(method, model, options) {
		var store = model.localStorage || model.collection.localStorage;
		var resp, errorMessage, syncDfd = $.Deferred && $.Deferred(); //If $ is having Deferred - use it.

		try {

			switch (method) {
			case "read":
				resp = model.id != undefined ? store.find(model) : store.findAll();
				break;
			case "create":
				resp = store.create(model);
				break;
			case "update":
				resp = store.update(model);
				break;
			case "delete":
				resp = store.destroy(model);
				break;
			}

		} catch(error) {
			if (error.code === DOMException.QUOTA_EXCEEDED_ERR && window.localStorage.length === 0)
				errorMessage = "Private browsing is unsupported";
			else
				errorMessage = error.message;
		}

		if (resp) {
			model.trigger("sync", model, resp, options);
			if (options && options.success)
				options.success(resp);
			if (syncDfd)
				syncDfd.resolve(resp);

		} else {
			errorMessage = errorMessage ? errorMessage
					: "Record Not Found";

			if (options && options.error)
				options.error(errorMessage);
			if (syncDfd)
				syncDfd.reject(errorMessage);
		}

		// add compatibility with $.ajax
		// always execute callback for success and error
		if (options && options.complete) options.complete(resp);

		return syncDfd && syncDfd.promise();
	};


	// Override 'Backbone.sync' to default to localSync,
	// the original 'Backbone.sync' is still available in 'Backbone.ajaxSync'
	Backbone.sync = Backbone.LocalStorage.sync;

	return Backbone.LocalStorage;
	}));