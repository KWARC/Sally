(function() {

	var maxTries = 10;

	var saveRequestTypes =["sendMessage", "injectScripts", "log"]; 

	var appTries = 0; // how many times tried to get the app
	var appRequests = [];
	function isFunction(functionToCheck) {
		var getType = {};
		return functionToCheck && getType.toString.call(functionToCheck) === '[object Function]';
	};

	var appMock = {};

	for (var msgidx in saveRequestTypes) {
		var msg = saveRequestTypes[msgidx];
		appMock[msg] = (function (msg) {
			return function() {
				var t = [msg].concat(Array.prototype.slice.call(arguments));
				appRequests.push(t);
			}
		})(msg);
	}

	/**
The Communication object contains the client side logic for sending messages from Theo (the services displayed in Theo) to Sally.
	 */
	var Communication = {
			callbackId : 0, //
			callbackCache : {}, 

			injectScripts: function() {
				this.getApp().injectScripts();
			},

			getApp : function() {
				if (typeof(app) != "undefined") {
					if (appRequests.length > 0) {
						for (var idx in appRequests) {
							var appReq = appRequests[idx];
							// app.call or app.apply does not work as they are not defined in the Java class
							if (appReq[0] == "log") {
								app.log(appReq[1]);
							}
							if (appReq[0] == "injectScripts") {
								app.injectScripts();
							}
							if (appReq[0] == "sendMessage") {
								app.sendMessage(appReq[1], appReq[2]);
							}
						}
						appRequests = [];
					}
					return app;
				}

				if (appTries > maxTries) {
					appRequests = [];
				} else {
					appTries++;
					setTimeout(this.getApp, 500);
				}

				return appMock;
			},

			/**
	Used to send events back to Sally.
			 */
			sendMessage : function (message, callback) {
				//If the scripts have not been injected there in no point in proceeding further.
				if (typeof(message) == 'undefined')
					return;
				var mes = JSON.stringify(serialize(message));

				if (typeof(callback)=="undefined")
					this.getApp().sendMessage(mes);
				else {
					this.getApp().sendMessage(mes, this.generateCallbackId(callback).toString())
				}
			},
			/**
	This function generates a name for the callback and attaches it to the Communication object.
	This is done so that when we get something from Sally we can call the appropriate function
			 */
			generateCallbackId : function (callback) {
				var callbackID = this.callbackId++;
				this.callbackCache[callbackID] = callback;
				return callbackID;
			},

			runCallback : function(callbackID, arg) {
				if (isFunction(this.callbackCache[callbackID])) {
					this.callbackCache[callbackID].call(window, unserialize(arg));
				}
			}
	};

	window.Communication = Communication;
})();