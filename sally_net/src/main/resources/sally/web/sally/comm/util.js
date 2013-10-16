function serialize(message) {
	var stream = new PROTO.Base64Stream;
	message.SerializeToStream(stream);
	return {
			"type" : message.message_type_,
			"s" : stream.getString()
	};
}

function unserialize(message) {
	var msg = JSON.parse(message);
	
	var classString = msg.type;
	if (classString.match(/^[a-zA-Z\.]+$/)) {
		var restMessage = msg.s;
		var stream = new PROTO.Base64Stream(restMessage);
		message = eval("new " + classString);
		message.ParseFromStream(stream);
		return message;
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