function serialize(message, msgid) {
	var stream = new PROTO.Base64Stream;
	message.SerializeToStream(stream);
	if (typeof (msgid) == 'undefined')
		return {
			"type" : message.message_type_,
			"s" : stream.getString()
		};
	else
		return {
			"type" : message.message_type_,
			"s" : stream.getString(),
			"msgid" : msgid
		};

}

function unserialize(type, message, msgrid) {
	classString = type;
	if (classString.match(/^[a-zA-Z\.]+$/)) {
		restMessage = message;
		var stream = new PROTO.Base64Stream(restMessage);
		message = eval("new " + classString);
		message.ParseFromStream(stream);
		if (typeof (msgrid) == 'undefined')
			return {
				"message" : message
			};
		else
			return {
				"message" : message,
				"msgrid" : msgrid
			};
	} else
		return null;
}

function restore(commetmsg) {
	if (typeof (commetmsg.data.msgrid) == 'undefined')
		return unserialize(commetmsg.data.type, commetmsg.data.s);
	else
		return unserialize(commetmsg.data.type, commetmsg.data.s,
				commetmsg.data.msgrid);
}

document.addEventListener("SissiEvent", function(e) {
	console.log("EVENT=", e);
}, true, true);

function openNewWindow(params) {
	var el = document.createElement("sissi");
	var options = $.extend({
		"title" : "",
		"x" : 100,
		"y" : 100,
		"sizex" : 400,
		"sizey" : 400,
		"url" : "",
		"cookie" : ""
	}, params);

	$.each(options, function(key, val) {
		$(el).attr(key, val);
	});
	$(document.body).append(el);

	var evt = document.createEvent('Events');
	evt.initEvent('SissiEvent', true, false);
	evt.details = options;
	el.dispatchEvent(evt);
}

/**
 * This function dispatches an event to let the ConnectionWindow know that the
 * resources have arrived.
 * 
 * @param message -
 *            Protobuffer message containing the required data.
 */
function inject(message) {
	var el = document.createElement("resources");
	$(document.body).append(el);
	var evt = new CustomEvent("Resources", {
		detail : message,
		bubbles : true,
		cancelable : false
	});
	el.dispatchEvent(evt);
}