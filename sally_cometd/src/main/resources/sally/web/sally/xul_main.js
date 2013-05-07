(function ($) {
    var cometd = $.cometd;
    $(document)
        .ready(

    function () {

        /**
         * Event listener to send message to sally. Have to test
         * it. I had a problem with getting the message through
         * so I had to serialize it into JSON and send the
         * string.
         */
        document.addEventListener("MessageRelay",

        function (evt) {
            var message = JSON.parse(evt.detail);
            cometd.publish("/service/theo/message", message);
        }, true, true);

        function _connectionEstablished() {
            $('#body').append(
                '<div>CometD Connection Established</div>');
        }

        function _connectionBroken() {
            $('#body').append(
                '<div>CometD Connection Broken</div>');
        }

        function _connectionClosed() {
            $('#body').append(
                '<div>CometD Connection Closed</div>');
        }

        // Function that manages the connection status with the
        // Bayeux server
        var _connected = false;

        function _metaConnect(message) {
            if (cometd.isDisconnected()) {
                _connected = false;
                _connectionClosed();
                return;
            }

            var wasConnected = _connected;
            _connected = message.successful === true;
            if (!wasConnected && _connected) {
                _connectionEstablished();
            } else if (wasConnected && !_connected) {
                _connectionBroken();
            }
        }

        // Function invoked when first contacting the server and
        // when the server has lost the state of this client
        function _metaHandshake(handshake) {
            if (handshake.successful === true) {
                cometd.batch(function () {
                    cometd.subscribe(
                        '/service/theo/init',

                    function (message) {
                        $('#body')
                            .append(
                            '<div>Server Says: I should init now </div>');
                    });
                    cometd.subscribe(
                        '/service/theo/newWindow',

                    function (_message) {
                       
                        var message = restore(_message);
                        $('#body')
                            .append(
                            '<div>Server Says: ' + message + '</div>');
                       var cookie = null;
                       if(typeof(message.message.cookie) !== 'undefined')
                       	cookie = message.message.cookie;
                        openNewWindow({
                            "x": message.message.position.x,
                            "y": message.message.position.y,
                            "url": message.message.url,
                            "cookie":cookie
                        });
                    });
                    /**
                     * Listen for resource messages from
                     * the specified channel. Call the
                     * function injectResources when you
                     * receive a message.
                     * injectResources is declared in
                     * util.js.
                     */
                    cometd.subscribe(
                    		"/service/theo/message",
                    function (_message) {
                        inject(JSON.stringify(_message));
                    });

                    var whoami = new sally.WhoAmI;
                    whoami.clientType = sally.WhoAmI.ClientType.Theo;
                    whoami.environmentType = sally.WhoAmI.EnvironmentType.Desktop;
                    whoami.documentType = sally.WhoAmI.DocType.Spreadsheet;
                    cometd.publish(
                        '/service/theo/register',
                    serialize(whoami));
                });
            }
        }

        // Disconnect when the page unloads
        $(window).unload(function () {
            cometd.disconnect(true);
        });

        var cometURL = location.protocol + "//" + location.host + config.contextPath+"/cometd";
        cometd.configure({
            url: cometURL,
            logLevel: 'info'
        });

        cometd.addListener('/meta/handshake', _metaHandshake);
        cometd.addListener('/meta/connect', _metaConnect);

        cometd.handshake();
    });
})(jQuery);