var JSON;JSON||(JSON={}),function(){function str(a,b){var c,d,e,f,g=gap,h,i=b[a];i&&typeof i=="object"&&typeof i.toJSON=="function"&&(i=i.toJSON(a)),typeof rep=="function"&&(i=rep.call(b,a,i));switch(typeof i){case"string":return quote(i);case"number":return isFinite(i)?String(i):"null";case"boolean":case"null":return String(i);case"object":if(!i)return"null";gap+=indent,h=[];if(Object.prototype.toString.apply(i)==="[object Array]"){f=i.length;for(c=0;c<f;c+=1)h[c]=str(c,i)||"null";e=h.length===0?"[]":gap?"[\n"+gap+h.join(",\n"+gap)+"\n"+g+"]":"["+h.join(",")+"]",gap=g;return e}if(rep&&typeof rep=="object"){f=rep.length;for(c=0;c<f;c+=1)d=rep[c],typeof d=="string"&&(e=str(d,i),e&&h.push(quote(d)+(gap?": ":":")+e))}else for(d in i)Object.hasOwnProperty.call(i,d)&&(e=str(d,i),e&&h.push(quote(d)+(gap?": ":":")+e));e=h.length===0?"{}":gap?"{\n"+gap+h.join(",\n"+gap)+"\n"+g+"}":"{"+h.join(",")+"}",gap=g;return e}}function quote(a){escapable.lastIndex=0;return escapable.test(a)?'"'+a.replace(escapable,function(a){var b=meta[a];return typeof b=="string"?b:"\\u"+("0000"+a.charCodeAt(0).toString(16)).slice(-4)})+'"':'"'+a+'"'}function f(a){return a<10?"0"+a:a}"use strict",typeof Date.prototype.toJSON!="function"&&(Date.prototype.toJSON=function(a){return isFinite(this.valueOf())?this.getUTCFullYear()+"-"+f(this.getUTCMonth()+1)+"-"+f(this.getUTCDate())+"T"+f(this.getUTCHours())+":"+f(this.getUTCMinutes())+":"+f(this.getUTCSeconds())+"Z":null},String.prototype.toJSON=Number.prototype.toJSON=Boolean.prototype.toJSON=function(a){return this.valueOf()});var cx=/[\u0000\u00ad\u0600-\u0604\u070f\u17b4\u17b5\u200c-\u200f\u2028-\u202f\u2060-\u206f\ufeff\ufff0-\uffff]/g,escapable=/[\\\"\x00-\x1f\x7f-\x9f\u00ad\u0600-\u0604\u070f\u17b4\u17b5\u200c-\u200f\u2028-\u202f\u2060-\u206f\ufeff\ufff0-\uffff]/g,gap,indent,meta={"\b":"\\b","\t":"\\t","\n":"\\n","\f":"\\f","\r":"\\r",'"':'\\"',"\\":"\\\\"},rep;typeof JSON.stringify!="function"&&(JSON.stringify=function(a,b,c){var d;gap="",indent="";if(typeof c=="number")for(d=0;d<c;d+=1)indent+=" ";else typeof c=="string"&&(indent=c);rep=b;if(b&&typeof b!="function"&&(typeof b!="object"||typeof b.length!="number"))throw new Error("JSON.stringify");return str("",{"":a})}),typeof JSON.parse!="function"&&(JSON.parse=function(text,reviver){function walk(a,b){var c,d,e=a[b];if(e&&typeof e=="object")for(c in e)Object.hasOwnProperty.call(e,c)&&(d=walk(e,c),d!==undefined?e[c]=d:delete e[c]);return reviver.call(a,b,e)}var j;text=String(text),cx.lastIndex=0,cx.test(text)&&(text=text.replace(cx,function(a){return"\\u"+("0000"+a.charCodeAt(0).toString(16)).slice(-4)}));if(/^[\],:{}\s]*$/.test(text.replace(/\\(?:["\\\/bfnrt]|u[0-9a-fA-F]{4})/g,"@").replace(/"[^"\\\n\r]*"|true|false|null|-?\d+(?:\.\d*)?(?:[eE][+\-]?\d+)?/g,"]").replace(/(?:^|:|,)(?:\s*\[)+/g,""))){j=eval("("+text+")");return typeof reviver=="function"?walk({"":j},""):j}throw new SyntaxError("JSON.parse")})}()/*
 * Copyright (c) 2010 the original author or authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// Namespaces for the cometd implementation
this.org = this.org || {};
org.cometd = {};

org.cometd.JSON = {};
org.cometd.JSON.toJSON = org.cometd.JSON.fromJSON = function(object)
{
    throw 'Abstract';
};

org.cometd.Utils = {};

org.cometd.Utils.isString = function(value)
{
    if (value === undefined || value === null)
    {
        return false;
    }
    return typeof value === 'string' ||  value instanceof String;
};

org.cometd.Utils.isArray = function(value)
{
    if (value === undefined || value === null)
    {
        return false;
    }
    return value instanceof Array;
};

/**
 * Returns whether the given element is contained into the given array.
 * @param element the element to check presence for
 * @param array the array to check for the element presence
 * @return the index of the element, if present, or a negative index if the element is not present
 */
org.cometd.Utils.inArray = function(element, array)
{
    for (var i = 0; i < array.length; ++i)
    {
        if (element === array[i])
        {
            return i;
        }
    }
    return -1;
};

org.cometd.Utils.setTimeout = function(cometd, funktion, delay)
{
    return window.setTimeout(function()
    {
        try
        {
            funktion();
        }
        catch (x)
        {
            cometd._debug('Exception invoking timed function', funktion, x);
        }
    }, delay);
};

org.cometd.Utils.clearTimeout = function(timeoutHandle)
{
    window.clearTimeout(timeoutHandle);
};

/**
 * A registry for transports used by the Cometd object.
 */
org.cometd.TransportRegistry = function()
{
    var _types = [];
    var _transports = {};

    this.getTransportTypes = function()
    {
        return _types.slice(0);
    };

    this.findTransportTypes = function(version, crossDomain, url)
    {
        var result = [];
        for (var i = 0; i < _types.length; ++i)
        {
            var type = _types[i];
            if (_transports[type].accept(version, crossDomain, url) === true)
            {
                result.push(type);
            }
        }
        return result;
    };

    this.negotiateTransport = function(types, version, crossDomain, url)
    {
        for (var i = 0; i < _types.length; ++i)
        {
            var type = _types[i];
            for (var j = 0; j < types.length; ++j)
            {
                if (type === types[j])
                {
                    var transport = _transports[type];
                    if (transport.accept(version, crossDomain, url) === true)
                    {
                        return transport;
                    }
                }
            }
        }
        return null;
    };

    this.add = function(type, transport, index)
    {
        var existing = false;
        for (var i = 0; i < _types.length; ++i)
        {
            if (_types[i] === type)
            {
                existing = true;
                break;
            }
        }

        if (!existing)
        {
            if (typeof index !== 'number')
            {
                _types.push(type);
            }
            else
            {
                _types.splice(index, 0, type);
            }
            _transports[type] = transport;
        }

        return !existing;
    };

    this.find = function(type)
    {
        for (var i = 0; i < _types.length; ++i)
        {
            if (_types[i] === type)
            {
                return _transports[type];
            }
        }
        return null;
    };

    this.remove = function(type)
    {
        for (var i = 0; i < _types.length; ++i)
        {
            if (_types[i] === type)
            {
                _types.splice(i, 1);
                var transport = _transports[type];
                delete _transports[type];
                return transport;
            }
        }
        return null;
    };

    this.clear = function()
    {
        _types = [];
        _transports = {};
    };

    this.reset = function()
    {
        for (var i = 0; i < _types.length; ++i)
        {
            _transports[_types[i]].reset();
        }
    };
};

/**
 * Base object with the common functionality for transports.
 */
org.cometd.Transport = function()
{
    var _type;
    var _cometd;

    /**
     * Function invoked just after a transport has been successfully registered.
     * @param type the type of transport (for example 'long-polling')
     * @param cometd the cometd object this transport has been registered to
     * @see #unregistered()
     */
    this.registered = function(type, cometd)
    {
        _type = type;
        _cometd = cometd;
    };

    /**
     * Function invoked just after a transport has been successfully unregistered.
     * @see #registered(type, cometd)
     */
    this.unregistered = function()
    {
        _type = null;
        _cometd = null;
    };

    this._debug = function()
    {
        _cometd._debug.apply(_cometd, arguments);
    };

    this._mixin = function()
    {
        return _cometd._mixin.apply(_cometd, arguments);
    };

    this.getConfiguration = function()
    {
        return _cometd.getConfiguration();
    };

    this.getAdvice = function()
    {
        return _cometd.getAdvice();
    };

    this.setTimeout = function(funktion, delay)
    {
        return org.cometd.Utils.setTimeout(_cometd, funktion, delay);
    };

    this.clearTimeout = function(handle)
    {
        org.cometd.Utils.clearTimeout(handle);
    };

    /**
     * Converts the given response into an array of bayeux messages
     * @param response the response to convert
     * @return an array of bayeux messages obtained by converting the response
     */
    this.convertToMessages = function (response)
    {
        if (org.cometd.Utils.isString(response))
        {
            try
            {
                return org.cometd.JSON.fromJSON(response);
            }
            catch(x)
            {
                this._debug('Could not convert to JSON the following string', '"' + response + '"');
                throw x;
            }
        }
        if (org.cometd.Utils.isArray(response))
        {
            return response;
        }
        if (response === undefined || response === null)
        {
            return [];
        }
        if (response instanceof Object)
        {
            return [response];
        }
        throw 'Conversion Error ' + response + ', typeof ' + (typeof response);
    };

    /**
     * Returns whether this transport can work for the given version and cross domain communication case.
     * @param version a string indicating the transport version
     * @param crossDomain a boolean indicating whether the communication is cross domain
     * @return true if this transport can work for the given version and cross domain communication case,
     * false otherwise
     */
    this.accept = function(version, crossDomain, url)
    {
        throw 'Abstract';
    };

    /**
     * Returns the type of this transport.
     * @see #registered(type, cometd)
     */
    this.getType = function()
    {
        return _type;
    };

    this.send = function(envelope, metaConnect)
    {
        throw 'Abstract';
    };

    this.reset = function()
    {
        this._debug('Transport', _type, 'reset');
    };

    this.abort = function()
    {
        this._debug('Transport', _type, 'aborted');
    };

    this.toString = function()
    {
        return this.getType();
    };
};

org.cometd.Transport.derive = function(baseObject)
{
    function F() {}
    F.prototype = baseObject;
    return new F();
};

/**
 * Base object with the common functionality for transports based on requests.
 * The key responsibility is to allow at most 2 outstanding requests to the server,
 * to avoid that requests are sent behind a long poll.
 * To achieve this, we have one reserved request for the long poll, and all other
 * requests are serialized one after the other.
 */
org.cometd.RequestTransport = function()
{
    var _super = new org.cometd.Transport();
    var _self = org.cometd.Transport.derive(_super);
    var _requestIds = 0;
    var _metaConnectRequest = null;
    var _requests = [];
    var _envelopes = [];

    function _coalesceEnvelopes(envelope)
    {
        while (_envelopes.length > 0)
        {
            var envelopeAndRequest = _envelopes[0];
            var newEnvelope = envelopeAndRequest[0];
            var newRequest = envelopeAndRequest[1];
            if (newEnvelope.url === envelope.url &&
                    newEnvelope.sync === envelope.sync)
            {
                _envelopes.shift();
                envelope.messages = envelope.messages.concat(newEnvelope.messages);
                this._debug('Coalesced', newEnvelope.messages.length, 'messages from request', newRequest.id);
                continue;
            }
            break;
        }
    }

    function _transportSend(envelope, request)
    {
        this.transportSend(envelope, request);
        request.expired = false;

        if (!envelope.sync)
        {
            var maxDelay = this.getConfiguration().maxNetworkDelay;
            var delay = maxDelay;
            if (request.metaConnect === true)
            {
                delay += this.getAdvice().timeout;
            }

            this._debug('Transport', this.getType(), 'waiting at most', delay, 'ms for the response, maxNetworkDelay', maxDelay);

            var self = this;
            request.timeout = this.setTimeout(function()
            {
                request.expired = true;
                var errorMessage = 'Request ' + request.id + ' of transport ' + self.getType() + ' exceeded ' + delay + ' ms max network delay';
                var failure = {
                    reason: errorMessage
                };
                var xhr = request.xhr;
                if (xhr)
                {
                    xhr.abort();
                    failure.httpCode = xhr.status;
                }
                self._debug(errorMessage);
                self.complete(request, false, request.metaConnect);
                envelope.onFailure(xhr, envelope.messages, failure);
            }, delay);
        }
    }

    function _queueSend(envelope)
    {
        var requestId = ++_requestIds;
        var request = {
            id: requestId,
            metaConnect: false
        };

        // Consider the metaConnect requests which should always be present
        if (_requests.length < this.getConfiguration().maxConnections - 1)
        {
            _requests.push(request);
            _transportSend.call(this, envelope, request);
        }
        else
        {
            this._debug('Transport', this.getType(), 'queueing request', requestId, 'envelope', envelope);
            _envelopes.push([envelope, request]);
        }
    }

    function _metaConnectComplete(request)
    {
        var requestId = request.id;
        this._debug('Transport', this.getType(), 'metaConnect complete, request', requestId);
        if (_metaConnectRequest !== null && _metaConnectRequest.id !== requestId)
        {
            throw 'Longpoll request mismatch, completing request ' + requestId;
        }

        // Reset metaConnect request
        _metaConnectRequest = null;
    }

    function _complete(request, success)
    {
        var index = org.cometd.Utils.inArray(request, _requests);
        // The index can be negative if the request has been aborted
        if (index >= 0)
        {
            _requests.splice(index, 1);
        }

        if (_envelopes.length > 0)
        {
            var envelopeAndRequest = _envelopes.shift();
            var nextEnvelope = envelopeAndRequest[0];
            var nextRequest = envelopeAndRequest[1];
            this._debug('Transport dequeued request', nextRequest.id);
            if (success)
            {
                if (this.getConfiguration().autoBatch)
                {
                    _coalesceEnvelopes.call(this, nextEnvelope);
                }
                _queueSend.call(this, nextEnvelope);
                this._debug('Transport completed request', request.id, nextEnvelope);
            }
            else
            {
                // Keep the semantic of calling response callbacks asynchronously after the request
                var self = this;
                this.setTimeout(function()
                {
                    self.complete(nextRequest, false, nextRequest.metaConnect);
                    var failure = {
                        reason: 'Previous request failed'
                    };
                    var xhr = nextRequest.xhr;
                    if (xhr)
                    {
                        failure.httpCode = xhr.status;
                    }
                    nextEnvelope.onFailure(xhr, nextEnvelope.messages, failure);
                }, 0);
            }
        }
    }

    _self.complete = function(request, success, metaConnect)
    {
        if (metaConnect)
        {
            _metaConnectComplete.call(this, request);
        }
        else
        {
            _complete.call(this, request, success);
        }
    };

    /**
     * Performs the actual send depending on the transport type details.
     * @param envelope the envelope to send
     * @param request the request information
     */
    _self.transportSend = function(envelope, request)
    {
        throw 'Abstract';
    };

    _self.transportSuccess = function(envelope, request, responses)
    {
        if (!request.expired)
        {
            this.clearTimeout(request.timeout);
            this.complete(request, true, request.metaConnect);
            if (responses && responses.length > 0)
            {
                envelope.onSuccess(responses);
            }
            else
            {
                envelope.onFailure(request.xhr, envelope.messages, {
                    httpCode: 204
                });
            }
        }
    };

    _self.transportFailure = function(envelope, request, failure)
    {
        if (!request.expired)
        {
            this.clearTimeout(request.timeout);
            this.complete(request, false, request.metaConnect);
            envelope.onFailure(request.xhr, envelope.messages, failure);
        }
    };

    function _metaConnectSend(envelope)
    {
        if (_metaConnectRequest !== null)
        {
            throw 'Concurrent metaConnect requests not allowed, request id=' + _metaConnectRequest.id + ' not yet completed';
        }

        var requestId = ++_requestIds;
        this._debug('Transport', this.getType(), 'metaConnect send, request', requestId, 'envelope', envelope);
        var request = {
            id: requestId,
            metaConnect: true
        };
        _transportSend.call(this, envelope, request);
        _metaConnectRequest = request;
    }

    _self.send = function(envelope, metaConnect)
    {
        if (metaConnect)
        {
            _metaConnectSend.call(this, envelope);
        }
        else
        {
            _queueSend.call(this, envelope);
        }
    };

    _self.abort = function()
    {
        _super.abort();
        for (var i = 0; i < _requests.length; ++i)
        {
            var request = _requests[i];
            this._debug('Aborting request', request);
            if (request.xhr)
            {
                request.xhr.abort();
            }
        }
        if (_metaConnectRequest)
        {
            this._debug('Aborting metaConnect request', _metaConnectRequest);
            if (_metaConnectRequest.xhr)
            {
                _metaConnectRequest.xhr.abort();
            }
        }
        this.reset();
    };

    _self.reset = function()
    {
        _super.reset();
        _metaConnectRequest = null;
        _requests = [];
        _envelopes = [];
    };

    return _self;
};

org.cometd.LongPollingTransport = function()
{
    var _super = new org.cometd.RequestTransport();
    var _self = org.cometd.Transport.derive(_super);
    // By default, support cross domain
    var _supportsCrossDomain = true;

    _self.accept = function(version, crossDomain, url)
    {
        return _supportsCrossDomain || !crossDomain;
    };

    _self.xhrSend = function(packet)
    {
        throw 'Abstract';
    };

    _self.transportSend = function(envelope, request)
    {
        this._debug('Transport', this.getType(), 'sending request', request.id, 'envelope', envelope);

        var self = this;
        try
        {
            var sameStack = true;
            request.xhr = this.xhrSend({
                transport: this,
                url: envelope.url,
                sync: envelope.sync,
                headers: this.getConfiguration().requestHeaders,
                body: org.cometd.JSON.toJSON(envelope.messages),
                onSuccess: function(response)
                {
                    self._debug('Transport', self.getType(), 'received response', response);
                    var success = false;
                    try
                    {
                        var received = self.convertToMessages(response);
                        if (received.length === 0)
                        {
                            _supportsCrossDomain = false;
                            self.transportFailure(envelope, request, {
                                httpCode: 204
                            });
                        }
                        else
                        {
                            success = true;
                            self.transportSuccess(envelope, request, received);
                        }
                    }
                    catch(x)
                    {
                        self._debug(x);
                        if (!success)
                        {
                            _supportsCrossDomain = false;
                            var failure = {
                                exception: x
                            };
                            var xhr = request.xhr;
                            if (xhr)
                            {
                                failure.httpCode = xhr.status;
                            }
                            self.transportFailure(envelope, request, failure);
                        }
                    }
                },
                onError: function(reason, exception)
                {
                    _supportsCrossDomain = false;
                    var failure = {
                        reason: reason,
                        exception: exception
                    };
                    var xhr = request.xhr;
                    if (xhr)
                    {
                        failure.httpCode = xhr.status;
                    }
                    if (sameStack)
                    {
                        // Keep the semantic of calling response callbacks asynchronously after the request
                        self.setTimeout(function()
                        {
                            self.transportFailure(envelope, request, failure);
                        }, 0);
                    }
                    else
                    {
                        self.transportFailure(envelope, request, failure);
                    }
                }
            });
            sameStack = false;
        }
        catch (x)
        {
            _supportsCrossDomain = false;
            // Keep the semantic of calling response callbacks asynchronously after the request
            this.setTimeout(function()
            {
                self.transportFailure(envelope, request, {
                    exception: x
                });
            }, 0);
        }
    };

    _self.reset = function()
    {
        _super.reset();
        _supportsCrossDomain = true;
    };

    return _self;
};

org.cometd.CallbackPollingTransport = function()
{
    var _super = new org.cometd.RequestTransport();
    var _self = org.cometd.Transport.derive(_super);
    var _maxLength = 2000;

    _self.accept = function(version, crossDomain, url)
    {
        return true;
    };

    _self.jsonpSend = function(packet)
    {
        throw 'Abstract';
    };

    _self.transportSend = function(envelope, request)
    {
        var self = this;

        // Microsoft Internet Explorer has a 2083 URL max length
        // We must ensure that we stay within that length
        var start = 0;
        var length = envelope.messages.length;
        var lengths = [];
        while (length > 0)
        {
            // Encode the messages because all brackets, quotes, commas, colons, etc
            // present in the JSON will be URL encoded, taking many more characters
            var json = org.cometd.JSON.toJSON(envelope.messages.slice(start, start + length));
            var urlLength = envelope.url.length + encodeURI(json).length;

            // Let's stay on the safe side and use 2000 instead of 2083
            // also because we did not count few characters among which
            // the parameter name 'message' and the parameter 'jsonp',
            // which sum up to about 50 chars
            if (urlLength > _maxLength)
            {
                if (length === 1)
                {
                    // Keep the semantic of calling response callbacks asynchronously after the request
                    this.setTimeout(function()
                    {
                        self.transportFailure(envelope, request, {
                            reason: 'Bayeux message too big, max is ' + _maxLength
                        });
                    }, 0);
                    return;
                }

                --length;
                continue;
            }

            lengths.push(length);
            start += length;
            length = envelope.messages.length - start;
        }

        // Here we are sure that the messages can be sent within the URL limit

        var envelopeToSend = envelope;
        if (lengths.length > 1)
        {
            var begin = 0;
            var end = lengths[0];
            this._debug('Transport', this.getType(), 'split', envelope.messages.length, 'messages into', lengths.join(' + '));
            envelopeToSend = this._mixin(false, {}, envelope);
            envelopeToSend.messages = envelope.messages.slice(begin, end);
            envelopeToSend.onSuccess = envelope.onSuccess;
            envelopeToSend.onFailure = envelope.onFailure;

            for (var i = 1; i < lengths.length; ++i)
            {
                var nextEnvelope = this._mixin(false, {}, envelope);
                begin = end;
                end += lengths[i];
                nextEnvelope.messages = envelope.messages.slice(begin, end);
                nextEnvelope.onSuccess = envelope.onSuccess;
                nextEnvelope.onFailure = envelope.onFailure;
                this.send(nextEnvelope, request.metaConnect);
            }
        }

        this._debug('Transport', this.getType(), 'sending request', request.id, 'envelope', envelopeToSend);

        try
        {
            var sameStack = true;
            this.jsonpSend({
                transport: this,
                url: envelopeToSend.url,
                sync: envelopeToSend.sync,
                headers: this.getConfiguration().requestHeaders,
                body: org.cometd.JSON.toJSON(envelopeToSend.messages),
                onSuccess: function(responses)
                {
                    var success = false;
                    try
                    {
                        var received = self.convertToMessages(responses);
                        if (received.length === 0)
                        {
                            self.transportFailure(envelopeToSend, request, {
                                httpCode: 204
                            });
                        }
                        else
                        {
                            success = true;
                            self.transportSuccess(envelopeToSend, request, received);
                        }
                    }
                    catch (x)
                    {
                        self._debug(x);
                        if (!success)
                        {
                            self.transportFailure(envelopeToSend, request, {
                                exception: x
                            });
                        }
                    }
                },
                onError: function(reason, exception)
                {
                    var failure = {
                        reason: reason,
                        exception: exception
                    };
                    if (sameStack)
                    {
                        // Keep the semantic of calling response callbacks asynchronously after the request
                        self.setTimeout(function()
                        {
                            self.transportFailure(envelopeToSend, request, failure);
                        }, 0);
                    }
                    else
                    {
                        self.transportFailure(envelopeToSend, request, failure);
                    }
                }
            });
            sameStack = false;
        }
        catch (xx)
        {
            // Keep the semantic of calling response callbacks asynchronously after the request
            this.setTimeout(function()
            {
                self.transportFailure(envelopeToSend, request, {
                    exception: xx
                });
            }, 0);
        }
    };

    return _self;
};

org.cometd.WebSocketTransport = function()
{
    var _super = new org.cometd.Transport();
    var _self = org.cometd.Transport.derive(_super);
    var _cometd;
    // By default, support WebSocket
    var _supportsWebSocket = true;
    // Whether we were able to establish a WebSocket connection
    var _webSocketSupported = false;
    // Envelopes that have been sent
    var _envelopes = {};
    // Timeouts for messages that have been sent
    var _timeouts = {};
    var _webSocket = null;
    var _opened = false;
    var _connected = false;
    var _successCallback;

    function _websocketConnect()
    {
        // Mangle the URL, changing the scheme from 'http' to 'ws'
        var url = _cometd.getURL().replace(/^http/, 'ws');
        this._debug('Transport', this.getType(), 'connecting to URL', url);

        var self = this;
        var connectTimer = null;

        var connectTimeout = _cometd.getConfiguration().connectTimeout;
        if (connectTimeout > 0)
        {
            connectTimer = this.setTimeout(function()
            {
                connectTimer = null;
                if (!_opened)
                {
                    self._debug('Transport', self.getType(), 'timed out while connecting to URL', url, ':', connectTimeout, 'ms');
                    self.onClose(1002, 'Connect Timeout');
                }
            }, connectTimeout);
        }

        var webSocket = new org.cometd.WebSocket(url);
        var onopen = function()
        {
            self._debug('WebSocket opened', webSocket);
            if (connectTimer)
            {
                self.clearTimeout(connectTimer);
                connectTimer = null;
            }
            if (webSocket !== _webSocket)
            {
                // It's possible that the onopen callback is invoked
                // with a delay so that we have already reconnected
                self._debug('Ignoring open event, WebSocket', _webSocket);
                return;
            }
            self.onOpen();
        };
        var onclose = function(event)
        {
            var code = event ? event.code : 1000;
            var reason = event ? event.reason : undefined;
            self._debug('WebSocket closed', code, '/', reason, webSocket);
            if (connectTimer)
            {
                self.clearTimeout(connectTimer);
                connectTimer = null;
            }
            if (webSocket !== _webSocket)
            {
                // The onclose callback may be invoked when the server sends
                // the close message reply, but after we have already reconnected
                self._debug('Ignoring close event, WebSocket', _webSocket);
                return;
            }
            self.onClose(code, reason);
        };
        var onmessage = function(message)
        {
            self._debug('WebSocket message', message, webSocket);
            if (webSocket !== _webSocket)
            {
                self._debug('Ignoring message event, WebSocket', _webSocket);
                return;
            }
            self.onMessage(message);
        };

        webSocket.onopen = onopen;
        webSocket.onclose = onclose;
        webSocket.onerror = function()
        {
            onclose({ code: 1002, reason: 'Error' });
        };
        webSocket.onmessage = onmessage;

        _webSocket = webSocket;
        this._debug('Transport', this.getType(), 'configured callbacks on', webSocket);
    }

    function _webSocketSend(envelope, metaConnect)
    {
        var json = org.cometd.JSON.toJSON(envelope.messages);

        _webSocket.send(json);
        this._debug('Transport', this.getType(), 'sent', envelope, 'metaConnect =', metaConnect);

        // Manage the timeout waiting for the response
        var maxDelay = this.getConfiguration().maxNetworkDelay;
        var delay = maxDelay;
        if (metaConnect)
        {
            delay += this.getAdvice().timeout;
            _connected = true;
        }

        var messageIds = [];
        for (var i = 0; i < envelope.messages.length; ++i)
        {
            var message = envelope.messages[i];
            if (message.id)
            {
                messageIds.push(message.id);
                var self = this;
                var webSocket = _webSocket;
                _timeouts[message.id] = this.setTimeout(function()
                {
                    if (webSocket)
                    {
                        webSocket.close(1000, 'Timeout');
                    }
                }, delay);
            }
        }

        this._debug('Transport', this.getType(), 'waiting at most', delay, 'ms for messages', messageIds, 'maxNetworkDelay', maxDelay, ', timeouts:', _timeouts);
    }

    function _send(envelope, metaConnect)
    {
        try
        {
            if (_webSocket === null)
            {
                _websocketConnect.call(this);
            }
            // We may have a non-null _webSocket, but not be open yet so
            // to avoid out of order deliveries, we check if we are open
            else if (_opened)
            {
                _webSocketSend.call(this, envelope, metaConnect);
            }
        }
        catch (x)
        {
            // Keep the semantic of calling response callbacks asynchronously after the request
            var webSocket = _webSocket;
            this.setTimeout(function()
            {
                envelope.onFailure(webSocket, envelope.messages, {
                    exception: x
                });
            }, 0);
        }
    }

    _self.onOpen = function()
    {
        this._debug('Transport', this.getType(), 'opened', _webSocket);
        _opened = true;
        _webSocketSupported = true;

        this._debug('Sending pending messages', _envelopes);
        for (var key in _envelopes)
        {
            var element = _envelopes[key];
            var envelope = element[0];
            var metaConnect = element[1];
            // Store the success callback, which is independent from the envelope,
            // so that it can be used to notify arrival of messages.
            _successCallback = envelope.onSuccess;
            _webSocketSend.call(this, envelope, metaConnect);
        }
    };

    _self.onMessage = function(wsMessage)
    {
        this._debug('Transport', this.getType(), 'received websocket message', wsMessage, _webSocket);

        var close = false;
        var messages = this.convertToMessages(wsMessage.data);
        var messageIds = [];
        for (var i = 0; i < messages.length; ++i)
        {
            var message = messages[i];

            // Detect if the message is a response to a request we made.
            // If it's a meta message, for sure it's a response;
            // otherwise it's a publish message and publish responses lack the data field
            if (/^\/meta\//.test(message.channel) || message.data === undefined)
            {
                if (message.id)
                {
                    messageIds.push(message.id);

                    var timeout = _timeouts[message.id];
                    if (timeout)
                    {
                        this.clearTimeout(timeout);
                        delete _timeouts[message.id];
                        this._debug('Transport', this.getType(), 'removed timeout for message', message.id, ', timeouts', _timeouts);
                    }
                }
            }

            if ('/meta/connect' === message.channel)
            {
                _connected = false;
            }
            if ('/meta/disconnect' === message.channel && !_connected)
            {
                close = true;
            }
        }

        // Remove the envelope corresponding to the messages
        var removed = false;
        for (var j = 0; j < messageIds.length; ++j)
        {
            var id = messageIds[j];
            for (var key in _envelopes)
            {
                var ids = key.split(',');
                var index = org.cometd.Utils.inArray(id, ids);
                if (index >= 0)
                {
                    removed = true;
                    ids.splice(index, 1);
                    var envelope = _envelopes[key][0];
                    var metaConnect = _envelopes[key][1];
                    delete _envelopes[key];
                    if (ids.length > 0)
                    {
                        _envelopes[ids.join(',')] = [envelope, metaConnect];
                    }
                    break;
                }
            }
        }
        if (removed)
        {
            this._debug('Transport', this.getType(), 'removed envelope, envelopes', _envelopes);
        }

        _successCallback.call(this, messages);

        if (close)
        {
            _webSocket.close(1000, 'Disconnect');
        }
    };

    _self.onClose = function(code, reason)
    {
        this._debug('Transport', this.getType(), 'closed', code, reason, _webSocket);

        // Remember if we were able to connect
        // This close event could be due to server shutdown, and if it restarts we want to try websocket again
        _supportsWebSocket = _webSocketSupported;

        for (var id in _timeouts)
        {
            this.clearTimeout(_timeouts[id]);
        }
        _timeouts = {};

        for (var key in _envelopes)
        {
            var envelope = _envelopes[key][0];
            var metaConnect = _envelopes[key][1];
            if (metaConnect)
            {
                _connected = false;
            }
            envelope.onFailure(_webSocket, envelope.messages, {
                websocketCode: code,
                reason: reason
            });
        }
        _envelopes = {};

        if (_webSocket !== null && _opened)
        {
            _webSocket.close(1000, 'Close');
        }
        _opened = false;
        _webSocket = null;
    };

    _self.registered = function(type, cometd)
    {
        _super.registered(type, cometd);
        _cometd = cometd;
    };

    _self.accept = function(version, crossDomain, url)
    {
        // Using !! to return a boolean (and not the WebSocket object)
        return _supportsWebSocket && !!org.cometd.WebSocket && _cometd.websocketEnabled !== false;
    };

    _self.send = function(envelope, metaConnect)
    {
        this._debug('Transport', this.getType(), 'sending', envelope, 'metaConnect =', metaConnect);

        // Store the envelope in any case; if the websocket cannot be opened, we fail it in close()
        var messageIds = [];
        for (var i = 0; i < envelope.messages.length; ++i)
        {
            var message = envelope.messages[i];
            if (message.id)
            {
                messageIds.push(message.id);
            }
        }
        _envelopes[messageIds.join(',')] = [envelope, metaConnect];
        this._debug('Transport', this.getType(), 'stored envelope, envelopes', _envelopes);

        _send.call(this, envelope, metaConnect);
    };

    _self.abort = function()
    {
        _super.abort();
        if (_webSocket !== null)
        {
            try
            {
                _webSocket.close(1001);
            }
            catch (x)
            {
                // Firefox may throw, just ignore
                this._debug(x);
            }
        }
        this.reset();
    };

    _self.reset = function()
    {
        _super.reset();
        if (_webSocket !== null && _opened)
        {
            _webSocket.close(1000, 'Reset');
        }
        _supportsWebSocket = true;
        _webSocketSupported = false;
        _timeouts = {};
        _envelopes = {};
        _webSocket = null;
        _opened = false;
        _successCallback = null;
    };

    return _self;
};

/**
 * The constructor for a Cometd object, identified by an optional name.
 * The default name is the string 'default'.
 * In the rare case a page needs more than one Bayeux conversation,
 * a new instance can be created via:
 * <pre>
 * var bayeuxUrl2 = ...;
 *
 * // Dojo style
 * var cometd2 = new dojox.Cometd('another_optional_name');
 *
 * // jQuery style
 * var cometd2 = new $.Cometd('another_optional_name');
 *
 * cometd2.init({url: bayeuxUrl2});
 * </pre>
 * @param name the optional name of this cometd object
 */
// IMPLEMENTATION NOTES:
// Be very careful in not changing the function order and pass this file every time through JSLint (http://jslint.com)
// The only implied globals must be "dojo", "org" and "window", and check that there are no "unused" warnings
// Failing to pass JSLint may result in shrinkers/minifiers to create an unusable file.
org.cometd.Cometd = function(name)
{
    var _cometd = this;
    var _name = name || 'default';
    var _crossDomain = false;
    var _transports = new org.cometd.TransportRegistry();
    var _transport;
    var _status = 'disconnected';
    var _messageId = 0;
    var _clientId = null;
    var _batch = 0;
    var _messageQueue = [];
    var _internalBatch = false;
    var _listeners = {};
    var _backoff = 0;
    var _scheduledSend = null;
    var _extensions = [];
    var _advice = {};
    var _handshakeProps;
    var _publishCallbacks = {};
    var _reestablish = false;
    var _connected = false;
    var _config = {
        connectTimeout: 0,
        maxConnections: 2,
        backoffIncrement: 1000,
        maxBackoff: 60000,
        logLevel: 'info',
        reverseIncomingExtensions: true,
        maxNetworkDelay: 10000,
        requestHeaders: {},
        appendMessageTypeToURL: true,
        autoBatch: false,
        advice: {
            timeout: 60000,
            interval: 0,
            reconnect: 'retry'
        }
    };

    /**
     * Mixes in the given objects into the target object by copying the properties.
     * @param deep if the copy must be deep
     * @param target the target object
     * @param objects the objects whose properties are copied into the target
     */
    this._mixin = function(deep, target, objects)
    {
        var result = target || {};

        // Skip first 2 parameters (deep and target), and loop over the others
        for (var i = 2; i < arguments.length; ++i)
        {
            var object = arguments[i];

            if (object === undefined || object === null)
            {
                continue;
            }

            for (var propName in object)
            {
                var prop = object[propName];
                var targ = result[propName];

                // Avoid infinite loops
                if (prop === target)
                {
                    continue;
                }
                // Do not mixin undefined values
                if (prop === undefined)
                {
                    continue;
                }

                if (deep && typeof prop === 'object' && prop !== null)
                {
                    if (prop instanceof Array)
                    {
                        result[propName] = this._mixin(deep, targ instanceof Array ? targ : [], prop);
                    }
                    else
                    {
                        var source = typeof targ === 'object' && !(targ instanceof Array) ? targ : {};
                        result[propName] = this._mixin(deep, source, prop);
                    }
                }
                else
                {
                    result[propName] = prop;
                }
            }
        }

        return result;
    };

    function _isString(value)
    {
        return org.cometd.Utils.isString(value);
    }

    function _isFunction(value)
    {
        if (value === undefined || value === null)
        {
            return false;
        }
        return typeof value === 'function';
    }

    function _log(level, args)
    {
        if (window.console)
        {
            var logger = window.console[level];
            if (_isFunction(logger))
            {
                logger.apply(window.console, args);
            }
        }
    }

    this._warn = function()
    {
        _log('warn', arguments);
    };

    this._info = function()
    {
        if (_config.logLevel !== 'warn')
        {
            _log('info', arguments);
        }
    };

    this._debug = function()
    {
        if (_config.logLevel === 'debug')
        {
            _log('debug', arguments);
        }
    };

    /**
     * Returns whether the given hostAndPort is cross domain.
     * The default implementation checks against window.location.host
     * but this function can be overridden to make it work in non-browser
     * environments.
     *
     * @param hostAndPort the host and port in format host:port
     * @return whether the given hostAndPort is cross domain
     */
    this._isCrossDomain = function(hostAndPort)
    {
        return hostAndPort && hostAndPort !== window.location.host;
    };

    function _configure(configuration)
    {
        _cometd._debug('Configuring cometd object with', configuration);
        // Support old style param, where only the Bayeux server URL was passed
        if (_isString(configuration))
        {
            configuration = { url: configuration };
        }
        if (!configuration)
        {
            configuration = {};
        }

        _config = _cometd._mixin(false, _config, configuration);

        if (!_config.url)
        {
            throw 'Missing required configuration parameter \'url\' specifying the Bayeux server URL';
        }

        // Check if we're cross domain
        // [1] = protocol://, [2] = host:port, [3] = host, [4] = IPv6_host, [5] = IPv4_host, [6] = :port, [7] = port, [8] = uri, [9] = rest
        var urlParts = /(^https?:\/\/)?(((\[[^\]]+\])|([^:\/\?#]+))(:(\d+))?)?([^\?#]*)(.*)?/.exec(_config.url);
        var hostAndPort = urlParts[2];
        var uri = urlParts[8];
        var afterURI = urlParts[9];
        _crossDomain = _cometd._isCrossDomain(hostAndPort);

        // Check if appending extra path is supported
        if (_config.appendMessageTypeToURL)
        {
            if (afterURI !== undefined && afterURI.length > 0)
            {
                _cometd._info('Appending message type to URI ' + uri + afterURI + ' is not supported, disabling \'appendMessageTypeToURL\' configuration');
                _config.appendMessageTypeToURL = false;
            }
            else
            {
                var uriSegments = uri.split('/');
                var lastSegmentIndex = uriSegments.length - 1;
                if (uri.match(/\/$/))
                {
                    lastSegmentIndex -= 1;
                }
                if (uriSegments[lastSegmentIndex].indexOf('.') >= 0)
                {
                    // Very likely the CometD servlet's URL pattern is mapped to an extension, such as *.cometd
                    // It will be difficult to add the extra path in this case
                    _cometd._info('Appending message type to URI ' + uri + ' is not supported, disabling \'appendMessageTypeToURL\' configuration');
                    _config.appendMessageTypeToURL = false;
                }
            }
        }
    }

    function _clearSubscriptions()
    {
        for (var channel in _listeners)
        {
            var subscriptions = _listeners[channel];
            for (var i = 0; i < subscriptions.length; ++i)
            {
                var subscription = subscriptions[i];
                if (subscription && !subscription.listener)
                {
                    delete subscriptions[i];
                    _cometd._debug('Removed subscription', subscription, 'for channel', channel);
                }
            }
        }
    }

    function _setStatus(newStatus)
    {
        if (_status !== newStatus)
        {
            _cometd._debug('Status', _status, '->', newStatus);
            _status = newStatus;
        }
    }

    function _isDisconnected()
    {
        return _status === 'disconnecting' || _status === 'disconnected';
    }

    function _nextMessageId()
    {
        return ++_messageId;
    }

    function _applyExtension(scope, callback, name, message, outgoing)
    {
        try
        {
            return callback.call(scope, message);
        }
        catch (x)
        {
            _cometd._debug('Exception during execution of extension', name, x);
            var exceptionCallback = _cometd.onExtensionException;
            if (_isFunction(exceptionCallback))
            {
                _cometd._debug('Invoking extension exception callback', name, x);
                try
                {
                    exceptionCallback.call(_cometd, x, name, outgoing, message);
                }
                catch(xx)
                {
                    _cometd._info('Exception during execution of exception callback in extension', name, xx);
                }
            }
            return message;
        }
    }

    function _applyIncomingExtensions(message)
    {
        for (var i = 0; i < _extensions.length; ++i)
        {
            if (message === undefined || message === null)
            {
                break;
            }

            var index = _config.reverseIncomingExtensions ? _extensions.length - 1 - i : i;
            var extension = _extensions[index];
            var callback = extension.extension.incoming;
            if (_isFunction(callback))
            {
                var result = _applyExtension(extension.extension, callback, extension.name, message, false);
                message = result === undefined ? message : result;
            }
        }
        return message;
    }

    function _applyOutgoingExtensions(message)
    {
        for (var i = 0; i < _extensions.length; ++i)
        {
            if (message === undefined || message === null)
            {
                break;
            }

            var extension = _extensions[i];
            var callback = extension.extension.outgoing;
            if (_isFunction(callback))
            {
                var result = _applyExtension(extension.extension, callback, extension.name, message, true);
                message = result === undefined ? message : result;
            }
        }
        return message;
    }

    function _notify(channel, message)
    {
        var subscriptions = _listeners[channel];
        if (subscriptions && subscriptions.length > 0)
        {
            for (var i = 0; i < subscriptions.length; ++i)
            {
                var subscription = subscriptions[i];
                // Subscriptions may come and go, so the array may have 'holes'
                if (subscription)
                {
                    try
                    {
                        subscription.callback.call(subscription.scope, message);
                    }
                    catch (x)
                    {
                        _cometd._debug('Exception during notification', subscription, message, x);
                        var listenerCallback = _cometd.onListenerException;
                        if (_isFunction(listenerCallback))
                        {
                            _cometd._debug('Invoking listener exception callback', subscription, x);
                            try
                            {
                                listenerCallback.call(_cometd, x, subscription.handle, subscription.listener, message);
                            }
                            catch (xx)
                            {
                                _cometd._info('Exception during execution of listener callback', subscription, xx);
                            }
                        }
                    }
                }
            }
        }
    }

    function _notifyListeners(channel, message)
    {
        // Notify direct listeners
        _notify(channel, message);

        // Notify the globbing listeners
        var channelParts = channel.split('/');
        var last = channelParts.length - 1;
        for (var i = last; i > 0; --i)
        {
            var channelPart = channelParts.slice(0, i).join('/') + '/*';
            // We don't want to notify /foo/* if the channel is /foo/bar/baz,
            // so we stop at the first non recursive globbing
            if (i === last)
            {
                _notify(channelPart, message);
            }
            // Add the recursive globber and notify
            channelPart += '*';
            _notify(channelPart, message);
        }
    }

    function _cancelDelayedSend()
    {
        if (_scheduledSend !== null)
        {
            org.cometd.Utils.clearTimeout(_scheduledSend);
        }
        _scheduledSend = null;
    }

    function _delayedSend(operation)
    {
        _cancelDelayedSend();
        var delay = _advice.interval + _backoff;
        _cometd._debug('Function scheduled in', delay, 'ms, interval =', _advice.interval, 'backoff =', _backoff, operation);
        _scheduledSend = org.cometd.Utils.setTimeout(_cometd, operation, delay);
    }

    // Needed to break cyclic dependencies between function definitions
    var _handleMessages;
    var _handleFailure;

    /**
     * Delivers the messages to the CometD server
     * @param messages the array of messages to send
     * @param longpoll true if this send is a long poll
     */
    function _send(sync, messages, longpoll, extraPath)
    {
        // We must be sure that the messages have a clientId.
        // This is not guaranteed since the handshake may take time to return
        // (and hence the clientId is not known yet) and the application
        // may create other messages.
        for (var i = 0; i < messages.length; ++i)
        {
            var message = messages[i];
            message.id = '' + _nextMessageId();

            if (_clientId)
            {
                message.clientId = _clientId;
            }

            var callback = undefined;
            if (_isFunction(message._callback))
            {
                callback = message._callback;
                // Remove the publish callback before calling the extensions
                delete message._callback;
            }

            message = _applyOutgoingExtensions(message);
            if (message !== undefined && message !== null)
            {
                messages[i] = message;
                if (callback)
                    _publishCallbacks[message.id] = callback;
            }
            else
            {
                messages.splice(i--, 1);
            }
        }

        if (messages.length === 0)
        {
            return;
        }

        var url = _config.url;
        if (_config.appendMessageTypeToURL)
        {
            // If url does not end with '/', then append it
            if (!url.match(/\/$/))
            {
                url = url + '/';
            }
            if (extraPath)
            {
                url = url + extraPath;
            }
        }

        var envelope = {
            url: url,
            sync: sync,
            messages: messages,
            onSuccess: function(rcvdMessages)
            {
                try
                {
                    _handleMessages.call(_cometd, rcvdMessages);
                }
                catch (x)
                {
                    _cometd._debug('Exception during handling of messages', x);
                }
            },
            onFailure: function(conduit, messages, failure)
            {
                try
                {
                    failure.connectionType = _cometd.getTransport().getType();
                    _handleFailure.call(_cometd, conduit, messages, failure);
                }
                catch (x)
                {
                    _cometd._debug('Exception during handling of failure', x);
                }
            }
        };
        _cometd._debug('Send', envelope);
        _transport.send(envelope, longpoll);
    }

    function _queueSend(message)
    {
        if (_batch > 0 || _internalBatch === true)
        {
            _messageQueue.push(message);
        }
        else
        {
            _send(false, [message], false);
        }
    }

    /**
     * Sends a complete bayeux message.
     * This method is exposed as a public so that extensions may use it
     * to send bayeux message directly, for example in case of re-sending
     * messages that have already been sent but that for some reason must
     * be resent.
     */
    this.send = _queueSend;

    function _resetBackoff()
    {
        _backoff = 0;
    }

    function _increaseBackoff()
    {
        if (_backoff < _config.maxBackoff)
        {
            _backoff += _config.backoffIncrement;
        }
    }

    /**
     * Starts a the batch of messages to be sent in a single request.
     * @see #_endBatch(sendMessages)
     */
    function _startBatch()
    {
        ++_batch;
    }

    function _flushBatch()
    {
        var messages = _messageQueue;
        _messageQueue = [];
        if (messages.length > 0)
        {
            _send(false, messages, false);
        }
    }

    /**
     * Ends the batch of messages to be sent in a single request,
     * optionally sending messages present in the message queue depending
     * on the given argument.
     * @see #_startBatch()
     */
    function _endBatch()
    {
        --_batch;
        if (_batch < 0)
        {
            throw 'Calls to startBatch() and endBatch() are not paired';
        }

        if (_batch === 0 && !_isDisconnected() && !_internalBatch)
        {
            _flushBatch();
        }
    }

    /**
     * Sends the connect message
     */
    function _connect()
    {
        if (!_isDisconnected())
        {
            var message = {
                channel: '/meta/connect',
                connectionType: _transport.getType()
            };

            // In case of reload or temporary loss of connection
            // we want the next successful connect to return immediately
            // instead of being held by the server, so that connect listeners
            // can be notified that the connection has been re-established
            if (!_connected)
            {
                message.advice = { timeout: 0 };
            }

            _setStatus('connecting');
            _cometd._debug('Connect sent', message);
            _send(false, [message], true, 'connect');
            _setStatus('connected');
        }
    }

    function _delayedConnect()
    {
        _setStatus('connecting');
        _delayedSend(function()
        {
            _connect();
        });
    }

    function _updateAdvice(newAdvice)
    {
        if (newAdvice)
        {
            _advice = _cometd._mixin(false, {}, _config.advice, newAdvice);
            _cometd._debug('New advice', _advice);
        }
    }

    function _disconnect(abort)
    {
        _cancelDelayedSend();
        if (abort)
        {
            _transport.abort();
        }
        _clientId = null;
        _setStatus('disconnected');
        _batch = 0;
        _resetBackoff();

        // Fail any existing queued message
        if (_messageQueue.length > 0)
        {
            _handleFailure.call(_cometd, undefined, _messageQueue, {
                reason: 'Disconnected'
            });
            _messageQueue = [];
        }
    }

    /**
     * Sends the initial handshake message
     */
    function _handshake(handshakeProps)
    {
        _clientId = null;

        _clearSubscriptions();

        // Reset the transports if we're not retrying the handshake
        if (_isDisconnected())
        {
            _transports.reset();
            _updateAdvice(_config.advice);
        }
        else
        {
            // We are retrying the handshake, either because another handshake failed
            // and we're backing off, or because the server timed us out and asks us to
            // re-handshake: in both cases, make sure that if the handshake succeeds
            // the next action is a connect.
            _updateAdvice(_cometd._mixin(false, _advice, {reconnect: 'retry'}));
        }

        _batch = 0;

        // Mark the start of an internal batch.
        // This is needed because handshake and connect are async.
        // It may happen that the application calls init() then subscribe()
        // and the subscribe message is sent before the connect message, if
        // the subscribe message is not held until the connect message is sent.
        // So here we start a batch to hold temporarily any message until
        // the connection is fully established.
        _internalBatch = true;

        // Save the properties provided by the user, so that
        // we can reuse them during automatic re-handshake
        _handshakeProps = handshakeProps;

        var version = '1.0';

        // Figure out the transports to send to the server
        var transportTypes = _transports.findTransportTypes(version, _crossDomain, _config.url);

        var bayeuxMessage = {
            version: version,
            minimumVersion: '0.9',
            channel: '/meta/handshake',
            supportedConnectionTypes: transportTypes,
            advice: {
                timeout: _advice.timeout,
                interval: _advice.interval
            }
        };
        // Do not allow the user to mess with the required properties,
        // so merge first the user properties and *then* the bayeux message
        var message = _cometd._mixin(false, {}, _handshakeProps, bayeuxMessage);

        // Pick up the first available transport as initial transport
        // since we don't know if the server supports it
        _transport = _transports.negotiateTransport(transportTypes, version, _crossDomain, _config.url);
        _cometd._debug('Initial transport is', _transport.getType());

        // We started a batch to hold the application messages,
        // so here we must bypass it and send immediately.
        _setStatus('handshaking');
        _cometd._debug('Handshake sent', message);
        _send(false, [message], false, 'handshake');
    }

    function _delayedHandshake()
    {
        _setStatus('handshaking');

        // We will call _handshake() which will reset _clientId, but we want to avoid
        // that between the end of this method and the call to _handshake() someone may
        // call publish() (or other methods that call _queueSend()).
        _internalBatch = true;

        _delayedSend(function()
        {
            _handshake(_handshakeProps);
        });
    }

    function _failHandshake(message)
    {
        _notifyListeners('/meta/handshake', message);
        _notifyListeners('/meta/unsuccessful', message);

        // Only try again if we haven't been disconnected and
        // the advice permits us to retry the handshake
        var retry = !_isDisconnected() && _advice.reconnect !== 'none';
        if (retry)
        {
            _increaseBackoff();
            _delayedHandshake();
        }
        else
        {
            _disconnect(false);
        }
    }

    function _handshakeResponse(message)
    {
        if (message.successful)
        {
            // Save clientId, figure out transport, then follow the advice to connect
            _clientId = message.clientId;

            var newTransport = _transports.negotiateTransport(message.supportedConnectionTypes, message.version, _crossDomain, _config.url);
            if (newTransport === null)
            {
                throw 'Could not negotiate transport with server; client ' +
                      _transports.findTransportTypes(message.version, _crossDomain, _config.url) +
                      ', server ' + message.supportedConnectionTypes;
            }
            else if (_transport !== newTransport)
            {
                _cometd._debug('Transport', _transport, '->', newTransport);
                _transport = newTransport;
            }

            // End the internal batch and allow held messages from the application
            // to go to the server (see _handshake() where we start the internal batch).
            _internalBatch = false;
            _flushBatch();

            // Here the new transport is in place, as well as the clientId, so
            // the listeners can perform a publish() if they want.
            // Notify the listeners before the connect below.
            message.reestablish = _reestablish;
            _reestablish = true;
            _notifyListeners('/meta/handshake', message);

            var action = _isDisconnected() ? 'none' : _advice.reconnect;
            switch (action)
            {
                case 'retry':
                    _resetBackoff();
                    _delayedConnect();
                    break;
                case 'none':
                    _disconnect(false);
                    break;
                default:
                    throw 'Unrecognized advice action ' + action;
            }
        }
        else
        {
            _failHandshake(message);
        }
    }

    function _handshakeFailure(failure)
    {
        _failHandshake({
            successful: false,
            failure: failure,
            channel: '/meta/handshake',
            advice: {
                reconnect: 'retry',
                interval: _backoff
            }
        });
    }

    function _failConnect(message)
    {
        // Notify the listeners after the status change but before the next action
        _notifyListeners('/meta/connect', message);
        _notifyListeners('/meta/unsuccessful', message);

        // This may happen when the server crashed, the current clientId
        // will be invalid, and the server will ask to handshake again
        // Listeners can call disconnect(), so check the state after they run
        var action = _isDisconnected() ? 'none' : _advice.reconnect;
        switch (action)
        {
            case 'retry':
                _delayedConnect();
                _increaseBackoff();
                break;
            case 'handshake':
                // The current transport may be failed (e.g. network disconnection)
                // Reset the transports so the new handshake picks up the right one
                _transports.reset();
                _resetBackoff();
                _delayedHandshake();
                break;
            case 'none':
                _disconnect(false);
                break;
            default:
                throw 'Unrecognized advice action' + action;
        }
    }

    function _connectResponse(message)
    {
        _connected = message.successful;

        if (_connected)
        {
            _notifyListeners('/meta/connect', message);

            // Normally, the advice will say "reconnect: 'retry', interval: 0"
            // and the server will hold the request, so when a response returns
            // we immediately call the server again (long polling)
            // Listeners can call disconnect(), so check the state after they run
            var action = _isDisconnected() ? 'none' : _advice.reconnect;
            switch (action)
            {
                case 'retry':
                    _resetBackoff();
                    _delayedConnect();
                    break;
                case 'none':
                    _disconnect(false);
                    break;
                default:
                    throw 'Unrecognized advice action ' + action;
            }
        }
        else
        {
            _failConnect(message);
        }
    }

    function _connectFailure(failure)
    {
        _connected = false;
        _failConnect({
            successful: false,
            failure: failure,
            channel: '/meta/connect',
            advice: {
                reconnect: 'retry',
                interval: _backoff
            }
        });
    }

    function _failDisconnect(message)
    {
        _disconnect(true);
        _notifyListeners('/meta/disconnect', message);
        _notifyListeners('/meta/unsuccessful', message);
    }

    function _disconnectResponse(message)
    {
        if (message.successful)
        {
            _disconnect(false);
            _notifyListeners('/meta/disconnect', message);
        }
        else
        {
            _failDisconnect(message);
        }
    }

    function _disconnectFailure(failure)
    {
        _failDisconnect({
            successful: false,
            failure: failure,
            channel: '/meta/disconnect',
            advice: {
                reconnect: 'none',
                interval: 0
            }
        });
    }

    function _failSubscribe(message)
    {
        _notifyListeners('/meta/subscribe', message);
        _notifyListeners('/meta/unsuccessful', message);
    }

    function _subscribeResponse(message)
    {
        if (message.successful)
        {
            _notifyListeners('/meta/subscribe', message);
        }
        else
        {
            _failSubscribe(message);
        }
    }

    function _subscribeFailure(failure)
    {
        _failSubscribe({
            successful: false,
            failure: failure,
            channel: '/meta/subscribe',
            advice: {
                reconnect: 'none',
                interval: 0
            }
        });
    }

    function _failUnsubscribe(message)
    {
        _notifyListeners('/meta/unsubscribe', message);
        _notifyListeners('/meta/unsuccessful', message);
    }

    function _unsubscribeResponse(message)
    {
        if (message.successful)
        {
            _notifyListeners('/meta/unsubscribe', message);
        }
        else
        {
            _failUnsubscribe(message);
        }
    }

    function _unsubscribeFailure(failure)
    {
        _failUnsubscribe({
            successful: false,
            failure: failure,
            channel: '/meta/unsubscribe',
            advice: {
                reconnect: 'none',
                interval: 0
            }
        });
    }

    function _handlePublishCallback(message)
    {
        var callback = _publishCallbacks[message.id];
        if (_isFunction(callback))
        {
            delete _publishCallbacks[message.id];
            callback.call(_cometd, message);
        }
    }

    function _failMessage(message)
    {
        _handlePublishCallback(message);
        _notifyListeners('/meta/publish', message);
        _notifyListeners('/meta/unsuccessful', message);
    }

    function _messageResponse(message)
    {
        if (message.successful === undefined)
        {
            if (message.data)
            {
                // It is a plain message, and not a bayeux meta message
                _notifyListeners(message.channel, message);
            }
            else
            {
                _cometd._debug('Unknown message', message);
            }
        }
        else
        {
            if (message.successful)
            {
                _handlePublishCallback(message);
                _notifyListeners('/meta/publish', message);
            }
            else
            {
                _failMessage(message);
            }
        }
    }

    function _messageFailure(message, failure)
    {
        _failMessage({
            successful: false,
            failure: failure,
            channel: message.channel,
            advice: {
                reconnect: 'none',
                interval: 0
            }
        });
    }

    function _receive(message)
    {
        message = _applyIncomingExtensions(message);
        if (message === undefined || message === null)
        {
            return;
        }

        _updateAdvice(message.advice);

        var channel = message.channel;
        switch (channel)
        {
            case '/meta/handshake':
                _handshakeResponse(message);
                break;
            case '/meta/connect':
                _connectResponse(message);
                break;
            case '/meta/disconnect':
                _disconnectResponse(message);
                break;
            case '/meta/subscribe':
                _subscribeResponse(message);
                break;
            case '/meta/unsubscribe':
                _unsubscribeResponse(message);
                break;
            default:
                _messageResponse(message);
                break;
        }
    }

    /**
     * Receives a message.
     * This method is exposed as a public so that extensions may inject
     * messages simulating that they had been received.
     */
    this.receive = _receive;

    _handleMessages = function(rcvdMessages)
    {
        _cometd._debug('Received', rcvdMessages);

        for (var i = 0; i < rcvdMessages.length; ++i)
        {
            var message = rcvdMessages[i];
            _receive(message);
        }
    };

    _handleFailure = function(conduit, messages, failure)
    {
        _cometd._debug('handleFailure', conduit, messages, failure);

        for (var i = 0; i < messages.length; ++i)
        {
            var message = messages[i];
            var messageFailure = _cometd._mixin(false, { message: message, transport: conduit }, failure);
            var channel = message.channel;
            switch (channel)
            {
                case '/meta/handshake':
                    _handshakeFailure(messageFailure);
                    break;
                case '/meta/connect':
                    _connectFailure(messageFailure);
                    break;
                case '/meta/disconnect':
                    _disconnectFailure(messageFailure);
                    break;
                case '/meta/subscribe':
                    _subscribeFailure(messageFailure);
                    break;
                case '/meta/unsubscribe':
                    _unsubscribeFailure(messageFailure);
                    break;
                default:
                    _messageFailure(message, messageFailure);
                    break;
            }
        }
    };

    function _hasSubscriptions(channel)
    {
        var subscriptions = _listeners[channel];
        if (subscriptions)
        {
            for (var i = 0; i < subscriptions.length; ++i)
            {
                if (subscriptions[i])
                {
                    return true;
                }
            }
        }
        return false;
    }

    function _resolveScopedCallback(scope, callback)
    {
        var delegate = {
            scope: scope,
            method: callback
        };
        if (_isFunction(scope))
        {
            delegate.scope = undefined;
            delegate.method = scope;
        }
        else
        {
            if (_isString(callback))
            {
                if (!scope)
                {
                    throw 'Invalid scope ' + scope;
                }
                delegate.method = scope[callback];
                if (!_isFunction(delegate.method))
                {
                    throw 'Invalid callback ' + callback + ' for scope ' + scope;
                }
            }
            else if (!_isFunction(callback))
            {
                throw 'Invalid callback ' + callback;
            }
        }
        return delegate;
    }

    function _addListener(channel, scope, callback, isListener)
    {
        // The data structure is a map<channel, subscription[]>, where each subscription
        // holds the callback to be called and its scope.

        var delegate = _resolveScopedCallback(scope, callback);
        _cometd._debug('Adding listener on', channel, 'with scope', delegate.scope, 'and callback', delegate.method);

        var subscription = {
            channel: channel,
            scope: delegate.scope,
            callback: delegate.method,
            listener: isListener
        };

        var subscriptions = _listeners[channel];
        if (!subscriptions)
        {
            subscriptions = [];
            _listeners[channel] = subscriptions;
        }

        // Pushing onto an array appends at the end and returns the id associated with the element increased by 1.
        // Note that if:
        // a.push('a'); var hb=a.push('b'); delete a[hb-1]; var hc=a.push('c');
        // then:
        // hc==3, a.join()=='a',,'c', a.length==3
        var subscriptionID = subscriptions.push(subscription) - 1;
        subscription.id = subscriptionID;
        subscription.handle = [channel, subscriptionID];

        _cometd._debug('Added listener', subscription, 'for channel', channel, 'having id =', subscriptionID);

        // The subscription to allow removal of the listener is made of the channel and the index
        return subscription.handle;
    }

    function _removeListener(subscription)
    {
        var subscriptions = _listeners[subscription[0]];
        if (subscriptions)
        {
            delete subscriptions[subscription[1]];
            _cometd._debug('Removed listener', subscription);
        }
    }

    //
    // PUBLIC API
    //

    /**
     * Registers the given transport under the given transport type.
     * The optional index parameter specifies the "priority" at which the
     * transport is registered (where 0 is the max priority).
     * If a transport with the same type is already registered, this function
     * does nothing and returns false.
     * @param type the transport type
     * @param transport the transport object
     * @param index the index at which this transport is to be registered
     * @return true if the transport has been registered, false otherwise
     * @see #unregisterTransport(type)
     */
    this.registerTransport = function(type, transport, index)
    {
        var result = _transports.add(type, transport, index);
        if (result)
        {
            this._debug('Registered transport', type);

            if (_isFunction(transport.registered))
            {
                transport.registered(type, this);
            }
        }
        return result;
    };

    /**
     * @return an array of all registered transport types
     */
    this.getTransportTypes = function()
    {
        return _transports.getTransportTypes();
    };

    /**
     * Unregisters the transport with the given transport type.
     * @param type the transport type to unregister
     * @return the transport that has been unregistered,
     * or null if no transport was previously registered under the given transport type
     */
    this.unregisterTransport = function(type)
    {
        var transport = _transports.remove(type);
        if (transport !== null)
        {
            this._debug('Unregistered transport', type);

            if (_isFunction(transport.unregistered))
            {
                transport.unregistered();
            }
        }
        return transport;
    };

    this.unregisterTransports = function()
    {
        _transports.clear();
    };

    this.findTransport = function(name)
    {
        return _transports.find(name);
    };

    /**
     * Configures the initial Bayeux communication with the Bayeux server.
     * Configuration is passed via an object that must contain a mandatory field <code>url</code>
     * of type string containing the URL of the Bayeux server.
     * @param configuration the configuration object
     */
    this.configure = function(configuration)
    {
        _configure.call(this, configuration);
    };

    /**
     * Configures and establishes the Bayeux communication with the Bayeux server
     * via a handshake and a subsequent connect.
     * @param configuration the configuration object
     * @param handshakeProps an object to be merged with the handshake message
     * @see #configure(configuration)
     * @see #handshake(handshakeProps)
     */
    this.init = function(configuration, handshakeProps)
    {
        this.configure(configuration);
        this.handshake(handshakeProps);
    };

    /**
     * Establishes the Bayeux communication with the Bayeux server
     * via a handshake and a subsequent connect.
     * @param handshakeProps an object to be merged with the handshake message
     */
    this.handshake = function(handshakeProps)
    {
        _setStatus('disconnected');
        _reestablish = false;
        _handshake(handshakeProps);
    };

    /**
     * Disconnects from the Bayeux server.
     * It is possible to suggest to attempt a synchronous disconnect, but this feature
     * may only be available in certain transports (for example, long-polling may support
     * it, callback-polling certainly does not).
     * @param sync whether attempt to perform a synchronous disconnect
     * @param disconnectProps an object to be merged with the disconnect message
     */
    this.disconnect = function(sync, disconnectProps)
    {
        if (_isDisconnected())
        {
            return;
        }

        if (disconnectProps === undefined)
        {
            if (typeof sync !== 'boolean')
            {
                disconnectProps = sync;
                sync = false;
            }
        }

        var bayeuxMessage = {
            channel: '/meta/disconnect'
        };
        var message = this._mixin(false, {}, disconnectProps, bayeuxMessage);
        _setStatus('disconnecting');
        _send(sync === true, [message], false, 'disconnect');
    };

    /**
     * Marks the start of a batch of application messages to be sent to the server
     * in a single request, obtaining a single response containing (possibly) many
     * application reply messages.
     * Messages are held in a queue and not sent until {@link #endBatch()} is called.
     * If startBatch() is called multiple times, then an equal number of endBatch()
     * calls must be made to close and send the batch of messages.
     * @see #endBatch()
     */
    this.startBatch = function()
    {
        _startBatch();
    };

    /**
     * Marks the end of a batch of application messages to be sent to the server
     * in a single request.
     * @see #startBatch()
     */
    this.endBatch = function()
    {
        _endBatch();
    };

    /**
     * Executes the given callback in the given scope, surrounded by a {@link #startBatch()}
     * and {@link #endBatch()} calls.
     * @param scope the scope of the callback, may be omitted
     * @param callback the callback to be executed within {@link #startBatch()} and {@link #endBatch()} calls
     */
    this.batch = function(scope, callback)
    {
        var delegate = _resolveScopedCallback(scope, callback);
        this.startBatch();
        try
        {
            delegate.method.call(delegate.scope);
            this.endBatch();
        }
        catch (x)
        {
            this._debug('Exception during execution of batch', x);
            this.endBatch();
            throw x;
        }
    };

    /**
     * Adds a listener for bayeux messages, performing the given callback in the given scope
     * when a message for the given channel arrives.
     * @param channel the channel the listener is interested to
     * @param scope the scope of the callback, may be omitted
     * @param callback the callback to call when a message is sent to the channel
     * @returns the subscription handle to be passed to {@link #removeListener(object)}
     * @see #removeListener(subscription)
     */
    this.addListener = function(channel, scope, callback)
    {
        if (arguments.length < 2)
        {
            throw 'Illegal arguments number: required 2, got ' + arguments.length;
        }
        if (!_isString(channel))
        {
            throw 'Illegal argument type: channel must be a string';
        }

        return _addListener(channel, scope, callback, true);
    };

    /**
     * Removes the subscription obtained with a call to {@link #addListener(string, object, function)}.
     * @param subscription the subscription to unsubscribe.
     * @see #addListener(channel, scope, callback)
     */
    this.removeListener = function(subscription)
    {
        if (!org.cometd.Utils.isArray(subscription))
        {
            throw 'Invalid argument: expected subscription, not ' + subscription;
        }

        _removeListener(subscription);
    };

    /**
     * Removes all listeners registered with {@link #addListener(channel, scope, callback)} or
     * {@link #subscribe(channel, scope, callback)}.
     */
    this.clearListeners = function()
    {
        _listeners = {};
    };

    /**
     * Subscribes to the given channel, performing the given callback in the given scope
     * when a message for the channel arrives.
     * @param channel the channel to subscribe to
     * @param scope the scope of the callback, may be omitted
     * @param callback the callback to call when a message is sent to the channel
     * @param subscribeProps an object to be merged with the subscribe message
     * @return the subscription handle to be passed to {@link #unsubscribe(object)}
     */
    this.subscribe = function(channel, scope, callback, subscribeProps)
    {
        if (arguments.length < 2)
        {
            throw 'Illegal arguments number: required 2, got ' + arguments.length;
        }
        if (!_isString(channel))
        {
            throw 'Illegal argument type: channel must be a string';
        }
        if (_isDisconnected())
        {
            throw 'Illegal state: already disconnected';
        }

        // Normalize arguments
        if (_isFunction(scope))
        {
            subscribeProps = callback;
            callback = scope;
            scope = undefined;
        }

        // Only send the message to the server if this client has not yet subscribed to the channel
        var send = !_hasSubscriptions(channel);

        var subscription = _addListener(channel, scope, callback, false);

        if (send)
        {
            // Send the subscription message after the subscription registration to avoid
            // races where the server would send a message to the subscribers, but here
            // on the client the subscription has not been added yet to the data structures
            var bayeuxMessage = {
                channel: '/meta/subscribe',
                subscription: channel
            };
            var message = this._mixin(false, {}, subscribeProps, bayeuxMessage);
            _queueSend(message);
        }

        return subscription;
    };

    /**
     * Unsubscribes the subscription obtained with a call to {@link #subscribe(string, object, function)}.
     * @param subscription the subscription to unsubscribe.
     */
    this.unsubscribe = function(subscription, unsubscribeProps)
    {
        if (arguments.length < 1)
        {
            throw 'Illegal arguments number: required 1, got ' + arguments.length;
        }
        if (_isDisconnected())
        {
            throw 'Illegal state: already disconnected';
        }

        // Remove the local listener before sending the message
        // This ensures that if the server fails, this client does not get notifications
        this.removeListener(subscription);

        var channel = subscription[0];
        // Only send the message to the server if this client unsubscribes the last subscription
        if (!_hasSubscriptions(channel))
        {
            var bayeuxMessage = {
                channel: '/meta/unsubscribe',
                subscription: channel
            };
            var message = this._mixin(false, {}, unsubscribeProps, bayeuxMessage);
            _queueSend(message);
        }
    };

    /**
     * Removes all subscriptions added via {@link #subscribe(channel, scope, callback, subscribeProps)},
     * but does not remove the listeners added via {@link addListener(channel, scope, callback)}.
     */
    this.clearSubscriptions = function()
    {
        _clearSubscriptions();
    };

    /**
     * Publishes a message on the given channel, containing the given content.
     * @param channel the channel to publish the message to
     * @param content the content of the message
     * @param publishProps an object to be merged with the publish message
     */
    this.publish = function(channel, content, publishProps, publishCallback)
    {
        if (arguments.length < 1)
        {
            throw 'Illegal arguments number: required 1, got ' + arguments.length;
        }
        if (!_isString(channel))
        {
            throw 'Illegal argument type: channel must be a string';
        }
        if (_isDisconnected())
        {
            throw 'Illegal state: already disconnected';
        }

        if (_isFunction(content))
        {
            publishCallback = content;
            content = publishProps = {};
        }
        else if (_isFunction(publishProps))
        {
            publishCallback = publishProps;
            publishProps = {};
        }

        var bayeuxMessage = {
            channel: channel,
            data: content,
            _callback: publishCallback
        };
        var message = this._mixin(false, {}, publishProps, bayeuxMessage);
        _queueSend(message);
    };

    /**
     * Returns a string representing the status of the bayeux communication with the Bayeux server.
     */
    this.getStatus = function()
    {
        return _status;
    };

    /**
     * Returns whether this instance has been disconnected.
     */
    this.isDisconnected = _isDisconnected;

    /**
     * Sets the backoff period used to increase the backoff time when retrying an unsuccessful or failed message.
     * Default value is 1 second, which means if there is a persistent failure the retries will happen
     * after 1 second, then after 2 seconds, then after 3 seconds, etc. So for example with 15 seconds of
     * elapsed time, there will be 5 retries (at 1, 3, 6, 10 and 15 seconds elapsed).
     * @param period the backoff period to set
     * @see #getBackoffIncrement()
     */
    this.setBackoffIncrement = function(period)
    {
        _config.backoffIncrement = period;
    };

    /**
     * Returns the backoff period used to increase the backoff time when retrying an unsuccessful or failed message.
     * @see #setBackoffIncrement(period)
     */
    this.getBackoffIncrement = function()
    {
        return _config.backoffIncrement;
    };

    /**
     * Returns the backoff period to wait before retrying an unsuccessful or failed message.
     */
    this.getBackoffPeriod = function()
    {
        return _backoff;
    };

    /**
     * Sets the log level for console logging.
     * Valid values are the strings 'error', 'warn', 'info' and 'debug', from
     * less verbose to more verbose.
     * @param level the log level string
     */
    this.setLogLevel = function(level)
    {
        _config.logLevel = level;
    };

    /**
     * Registers an extension whose callbacks are called for every incoming message
     * (that comes from the server to this client implementation) and for every
     * outgoing message (that originates from this client implementation for the
     * server).
     * The format of the extension object is the following:
     * <pre>
     * {
     *     incoming: function(message) { ... },
     *     outgoing: function(message) { ... }
     * }
     * </pre>
     * Both properties are optional, but if they are present they will be called
     * respectively for each incoming message and for each outgoing message.
     * @param name the name of the extension
     * @param extension the extension to register
     * @return true if the extension was registered, false otherwise
     * @see #unregisterExtension(name)
     */
    this.registerExtension = function(name, extension)
    {
        if (arguments.length < 2)
        {
            throw 'Illegal arguments number: required 2, got ' + arguments.length;
        }
        if (!_isString(name))
        {
            throw 'Illegal argument type: extension name must be a string';
        }

        var existing = false;
        for (var i = 0; i < _extensions.length; ++i)
        {
            var existingExtension = _extensions[i];
            if (existingExtension.name === name)
            {
                existing = true;
                break;
            }
        }
        if (!existing)
        {
            _extensions.push({
                name: name,
                extension: extension
            });
            this._debug('Registered extension', name);

            // Callback for extensions
            if (_isFunction(extension.registered))
            {
                extension.registered(name, this);
            }

            return true;
        }
        else
        {
            this._info('Could not register extension with name', name, 'since another extension with the same name already exists');
            return false;
        }
    };

    /**
     * Unregister an extension previously registered with
     * {@link #registerExtension(name, extension)}.
     * @param name the name of the extension to unregister.
     * @return true if the extension was unregistered, false otherwise
     */
    this.unregisterExtension = function(name)
    {
        if (!_isString(name))
        {
            throw 'Illegal argument type: extension name must be a string';
        }

        var unregistered = false;
        for (var i = 0; i < _extensions.length; ++i)
        {
            var extension = _extensions[i];
            if (extension.name === name)
            {
                _extensions.splice(i, 1);
                unregistered = true;
                this._debug('Unregistered extension', name);

                // Callback for extensions
                var ext = extension.extension;
                if (_isFunction(ext.unregistered))
                {
                    ext.unregistered();
                }

                break;
            }
        }
        return unregistered;
    };

    /**
     * Find the extension registered with the given name.
     * @param name the name of the extension to find
     * @return the extension found or null if no extension with the given name has been registered
     */
    this.getExtension = function(name)
    {
        for (var i = 0; i < _extensions.length; ++i)
        {
            var extension = _extensions[i];
            if (extension.name === name)
            {
                return extension.extension;
            }
        }
        return null;
    };

    /**
     * Returns the name assigned to this Cometd object, or the string 'default'
     * if no name has been explicitly passed as parameter to the constructor.
     */
    this.getName = function()
    {
        return _name;
    };

    /**
     * Returns the clientId assigned by the Bayeux server during handshake.
     */
    this.getClientId = function()
    {
        return _clientId;
    };

    /**
     * Returns the URL of the Bayeux server.
     */
    this.getURL = function()
    {
        return _config.url;
    };

    this.getTransport = function()
    {
        return _transport;
    };

    this.getConfiguration = function()
    {
        return this._mixin(true, {}, _config);
    };

    this.getAdvice = function()
    {
        return this._mixin(true, {}, _advice);
    };

    // WebSocket handling for Firefox, which deploys WebSocket
    // under the name of MozWebSocket in Firefox 6, 7, 8 and 9
    org.cometd.WebSocket = window.WebSocket;
    if (!org.cometd.WebSocket)
    {
        org.cometd.WebSocket = window.MozWebSocket;
    }
};

if (typeof define === 'function' && define.amd)
{
    define(function()
    {
        return org.cometd;
    });
}

/*
 * Copyright (c) 2010 the original author or authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

(function($)
{
    function bind($, org_cometd)
    {
        // Remap cometd JSON functions to jquery JSON functions
        org_cometd.JSON.toJSON = JSON.stringify;
        org_cometd.JSON.fromJSON = JSON.parse;

        function _setHeaders(xhr, headers)
        {
            if (headers)
            {
                for (var headerName in headers)
                {
                    if (headerName.toLowerCase() === 'content-type')
                    {
                        continue;
                    }
                    xhr.setRequestHeader(headerName, headers[headerName]);
                }
            }
        }

        // Remap toolkit-specific transport calls
        function LongPollingTransport()
        {
            var _super = new org_cometd.LongPollingTransport();
            var that = org_cometd.Transport.derive(_super);

            that.xhrSend = function(packet)
            {
                return $.ajax({
                    url: packet.url,
                    async: packet.sync !== true,
                    type: 'POST',
                    contentType: 'application/json;charset=UTF-8',
                    data: packet.body,
                    xhrFields: {
                        // Has no effect if the request is not cross domain
                        // but if it is, allows cookies to be sent to the server
                        withCredentials: true
                    },
                    beforeSend: function(xhr)
                    {
                        _setHeaders(xhr, packet.headers);
                        // Returning false will abort the XHR send
                        return true;
                    },
                    success: packet.onSuccess,
                    error: function(xhr, reason, exception)
                    {
                        packet.onError(reason, exception);
                    }
                });
            };

            return that;
        }

        function CallbackPollingTransport()
        {
            var _super = new org_cometd.CallbackPollingTransport();
            var that = org_cometd.Transport.derive(_super);

            that.jsonpSend = function(packet)
            {
                $.ajax({
                    url: packet.url,
                    async: packet.sync !== true,
                    type: 'GET',
                    dataType: 'jsonp',
                    jsonp: 'jsonp',
                    data: {
                        // In callback-polling, the content must be sent via the 'message' parameter
                        message: packet.body
                    },
                    beforeSend: function(xhr)
                    {
                        _setHeaders(xhr, packet.headers);
                        // Returning false will abort the XHR send
                        return true;
                    },
                    success: packet.onSuccess,
                    error: function(xhr, reason, exception)
                    {
                        packet.onError(reason, exception);
                    }
                });
            };

            return that;
        }

        $.Cometd = function(name)
        {
            var cometd = new org_cometd.Cometd(name);

            // Registration order is important
            if (org_cometd.WebSocket)
            {
                cometd.registerTransport('websocket', new org_cometd.WebSocketTransport());
            }
            cometd.registerTransport('long-polling', new LongPollingTransport());
            cometd.registerTransport('callback-polling', new CallbackPollingTransport());

            return cometd;
        };

        // The default cometd instance
        $.cometd = new $.Cometd();

        return $.cometd;
    }

    bind($, org.cometd);
})(jQuery);
/* 
 * DataView.js:
 * An implementation of the DataView class on top of typed arrays.
 * Useful for Firefox 4 which implements TypedArrays but not DataView.
 *
 * Copyright 2011, David Flanagan
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without modification, 
 * are permitted provided that the following conditions are met:
 *
 *   Redistributions of source code must retain the above copyright notice, 
 *   this list of conditions and the following disclaimer.
 *
 *   Redistributions in binary form must reproduce the above copyright notice, 
 *   this list of conditions and the following disclaimer in the documentation.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" 
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE 
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE 
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE 
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE 
 * GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) 
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT 
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT 
 * OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
"use strict";

(function(global) {
    // If DataView already exists, do nothing
    if (global.DataView) return;

    // If ArrayBuffer is not supported, fail with an error
    if (!global.ArrayBuffer) fail("ArrayBuffer not supported");

    // If ES5 is not supported, fail
    if (!Object.defineProperties) fail("This module requires ECMAScript 5");

    // Figure if the platform is natively little-endian.
    // If the integer 0x00000001 is arranged in memory as 01 00 00 00 then
    // we're on a little endian platform. On a big-endian platform we'd get
    // get bytes 00 00 00 01 instead.
    var nativele = new Int8Array(new Int32Array([1]).buffer)[0] === 1;

    // A temporary array for copying or reversing bytes into.
    // Since js is single-threaded, we only need this one static copy
    var temp = new Uint8Array(8);

    // The DataView() constructor
    global.DataView = function DataView(buffer, offset, length) {
        if (!(buffer instanceof ArrayBuffer)) fail("Bad ArrayBuffer");

        // Default values for omitted arguments
        offset = offset || 0;
        length = length || (buffer.byteLength - offset);

        if (offset < 0 || length < 0 || offset+length > buffer.byteLength)
            fail("Illegal offset and/or length");

        // Define the 3 read-only, non-enumerable ArrayBufferView properties
        Object.defineProperties(this, {
            buffer: {
                value: buffer,
                enumerable:false, writable: false, configurable: false
            },
            byteOffset: {
                value: offset,
                enumerable:false, writable: false, configurable: false
            },
            byteLength: {
                value: length,
                enumerable:false, writable: false, configurable: false
            },
            _bytes: {
                value: new Uint8Array(buffer, offset, length),
                enumerable:false, writable: false, configurable: false
            }
        });
    }

    // The DataView prototype object
    global.DataView.prototype = {
        constructor: DataView,
        
        getInt8: function getInt8(offset) {
            return get(this, Int8Array, 1, offset);
        },
        getUint8: function getUint8(offset) {
            return get(this, Uint8Array, 1, offset);
        },
        getInt16: function getInt16(offset, le) {
            return get(this, Int16Array, 2, offset, le);
        },
        getUint16: function getUint16(offset, le) {
            return get(this, Uint16Array, 2, offset, le);
        },
        getInt32: function getInt32(offset, le) {
            return get(this, Int32Array, 4, offset, le);
        },
        getUint32: function getUint32(offset, le) {
            return get(this, Uint32Array, 4, offset, le);
        },
        getFloat32: function getFloat32(offset, le) {
            return get(this, Float32Array, 4, offset, le);
        },
        getFloat64: function getFloat32(offset, le) {
            return get(this, Float64Array, 8, offset, le);
        },

        
        setInt8: function setInt8(offset, value) {
            set(this, Int8Array, 1, offset, value);
        },
        setUint8: function setUint8(offset, value) {
            set(this, Uint8Array, 1, offset, value);
        },
        setInt16: function setInt16(offset, value, le) {
            set(this, Int16Array, 2, offset, value, le);
        },
        setUint16: function setUint16(offset, value, le) {
            set(this, Uint16Array, 2, offset, value, le);
        },
        setInt32: function setInt32(offset, value, le) {
            set(this, Int32Array, 4, offset, value, le);
        },
        setUint32: function setUint32(offset, value, le) {
            set(this, Uint32Array, 4, offset, value, le);
        },
        setFloat32: function setFloat32(offset, value, le) {
            set(this, Float32Array, 4, offset, value, le);
        },
        setFloat64: function setFloat64(offset, value, le) {
            set(this, Float64Array, 8, offset, value, le);
        }
    };

    // The get() utility function used by the get methods
    function get(view, type, size, offset, le) {
        if (offset === undefined) fail("Missing required offset argument");

        if (offset < 0 || offset + size > view.byteLength)
            fail("Invalid index: " + offset);

        if (size === 1 || !!le === nativele) { 
            // This is the easy case: the desired endianness 
            // matches the native endianness.

            // Typed arrays require proper alignment.  DataView does not.
            if ((view.byteOffset + offset) % size === 0) 
                return (new type(view.buffer, view.byteOffset+offset, 1))[0];
            else {
                // Copy bytes into the temp array, to fix alignment
                for(var i = 0; i < size; i++) 
                    temp[i] = view._bytes[offset+i];
                // Now wrap that buffer with an array of the desired type
                return (new type(temp.buffer))[0];
            }
        }
        else {
            // If the native endianness doesn't match the desired, then
            // we have to reverse the bytes
            for(var i = 0; i < size; i++)
                temp[size-i-1] = view._bytes[offset+i];
            return (new type(temp.buffer))[0];
        }
    }

    // The set() utility function used by the set methods
    function set(view, type, size, offset, value, le) {
        if (offset === undefined) fail("Missing required offset argument");
        if (value === undefined) fail("Missing required value argument");

        if (offset < 0 || offset + size > view.byteLength)
            fail("Invalid index: " + offset);

        if (size === 1 || !!le === nativele) { 
            // This is the easy case: the desired endianness 
            // matches the native endianness.
            if ((view.byteOffset + offset) % size === 0) {
                (new type(view.buffer,view.byteOffset+offset, 1))[0] = value;
            }
            else {
                (new type(temp.buffer))[0] = value;
                // Now copy the bytes into the view's buffer
                for(var i = 0; i < size; i++)
                    view._bytes[i+offset] = temp[i];
            }
        }
        else {
            // If the native endianness doesn't match the desired, then
            // we have to reverse the bytes
            
            // Store the value into our temporary buffer
            (new type(temp.buffer))[0] = value;

            // Now copy the bytes, in reverse order, into the view's buffer
            for(var i = 0; i < size; i++)
                view._bytes[offset+i] = temp[size-1-i];
        }
    }

    function fail(msg) { throw new Error(msg); }
}(this));
/*  ProtoJS - Protocol buffers for Javascript.
 *  protobuf.js
 *
 *  Copyright (c) 2009-2010, Patrick Reiter Horn
 *  All rights reserved.
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions are
 *  met:
 *  * Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *  * Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 *  * Neither the name of ProtoJS nor the names of its contributors may
 *    be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
"use strict";

var PROTO = {};

PROTO.IsArray = (function() {
  if (typeof(Uint8Array) != "undefined") {
    return function(arr) {
      return arr instanceof Array || arr instanceof Uint8Array;
    };
  } else {
    return function(arr) {
      return arr instanceof Array;
    };
  }
})();

PROTO.DefineProperty = (function () {
        var DefineProperty;
        if (typeof(Object.defineProperty) != "undefined") {
            /**
             * @suppress {missingProperties}
             */
            DefineProperty = function(prototype, property, getter, setter) {
                Object.defineProperty(prototype, property, {
                    'get': getter, 'set': setter,
                    'enumerable': true, 'configurable': false});
            };
        } else if (Object.prototype.__defineGetter__ && Object.prototype.__defineSetter__) {
            DefineProperty = function(prototype, property, getter, setter) {
                if (typeof getter !== 'undefined') {
                    prototype.__defineGetter__(property, getter);
                }
                if (typeof setter !== 'undefined') {
                    prototype.__defineSetter__(property, setter);
                }
            };
        }
        // IE8's Object.defineProperty method might be broken.
        // Make sure DefineProperty works before returning it.
        if (DefineProperty) {
            try {
                /**
                 * @constructor
                 */
                var TestClass = function(){};
                DefineProperty(TestClass.prototype, "x",
                               function(){return this.xval*2;},
                               function(newx){this.xval=newx;});
                var testinst = new TestClass;
                testinst.x = 5;
                if (testinst.x != 10) {
                    PROTO.warn("DefineProperty test gave the wrong result "+testinst.x);
                    DefineProperty = undefined;
                }
            } catch (e) {
                PROTO.warn("DefineProperty should be supported, but threw "+e);
                DefineProperty = undefined;
            }
        }
        return DefineProperty;
})();

/** Clones a PROTO type object. Does not work on arbitrary javascript objects.
For example, can be used to copy the "bytes" class and make a custom toString method.
*/
PROTO.cloneType = function(f) {
    var ret = {};
    for (var x in f) {
        ret[x] = f[x];
    }
    return ret;
}

PROTO.wiretypes = {
    varint: 0,
    fixed64: 1,
    lengthdelim: 2,
    fixed32: 5
};

PROTO.optional = 'optional';
PROTO.repeated = 'repeated';
PROTO.required = 'required';
/**
 * @param {string} s
 */
PROTO.warn = function (s) {
    if (typeof(self.console)!="undefined" && self.console.log) {
        self.console.log(s);            
    }
};

/**
 * @constructor
 */
PROTO.I64 = function (msw, lsw, sign) {
    /**
     * @type {number}
     */
    this.msw = msw;
    /**
     * @type {number}
     */
    this.lsw = lsw;
    if (typeof lsw === undefined) {
        PROTO.warn("Too few arguments passed to I64 constructor: perhaps you meant PROTO.I64.fromNumber()");
        throw ("Too few arguments passed to I64 constructor: perhaps you meant PROTO.I64.fromNumber()");
    }
    if (sign === true) sign = -1;
    if (!sign) sign = 1;
    this.sign = sign;
};

PROTO.I64.prototype = {
    toNumber: function() {
        return (this.msw*4294967296 + this.lsw)*this.sign;
    },
    toString: function() {
        //return this.toNumber();
        function zeros(len){
            var retval="";
            for (var i=0;i<len;++i) {
                retval+="0";
            }
            return retval;
        }
        var firstHalf=this.msw.toString(16);
        var secondHalf=this.lsw.toString(16);
        var sign = (this.sign==-1 ? "-" : "");
        return sign+"0x"+zeros(8-firstHalf.length)+firstHalf+zeros(8-secondHalf.length)+secondHalf;
    },
    equals: function(other) {
        return this.sign==other.sign&&this.msw==other.msw&&this.lsw==other.lsw;
    },
    hash: function() {
        return (this.sign*this.msw)+"_"+this.lsw;
    },
    convertToUnsigned: function() {
        var local_lsw;
        local_lsw=this.lsw;
        var local_msw;
        if (this.sign<0) {
            local_msw=2147483647-this.msw;
            local_msw+=2147483647;
            local_msw+=1;
            local_lsw=2147483647-this.lsw;
            local_lsw+=2147483647;
            local_lsw+=2;
            if (local_lsw==4294967296) {
                local_lsw=0;
                local_msw+=1;
            }
        }else {
            local_msw=this.msw;
        }
        return new PROTO.I64(local_msw,local_lsw,1);
    },
    convertFromUnsigned:function() {
        if(this.msw>=2147483648) {
            var local_msw = 4294967295-this.msw;
            var local_lsw = 4294967295-this.lsw+1;
            if (local_lsw>4294967295) {
                local_lsw-=4294967296;
                local_msw+=1;
            }
            return new PROTO.I64(local_msw,local_lsw,-1);
        }
        return new PROTO.I64(this.msw,this.lsw,this.sign);
    },
    convertToZigzag: function() {
        var local_lsw;
        if (this.sign<0) {
            local_lsw=this.lsw*2-1;
        }else {
            local_lsw=this.lsw*2;
        }
        var local_msw=this.msw*2;
        if (local_lsw>4294967295){
            local_msw+=1;
            local_lsw-=4294967296;
        }
        if (local_lsw<0){
            local_msw-=1;
            local_lsw+=4294967296;
        }
        return new PROTO.I64(local_msw,local_lsw,1);
    },
    convertFromZigzag:function() {
        var retval;
        if(this.msw&1) {//carry the bit from the most significant to the least by adding 2^31 to lsw
            retval = new PROTO.I64((this.msw>>>1),
                                 2147483648+(this.lsw>>>1),
                                 (this.lsw&1)?-1:1);
        } else {
            retval = new PROTO.I64((this.msw>>>1),
                                   (this.lsw>>>1),
                                   (this.lsw&1)?-1:1);
        }
        if (retval.sign==-1) {
            retval.lsw+=1;
            if (retval.lsw>4294967295) {
                retval.msw+=1;
                retval.lsw-=4294967296;                
            }
        }
        return retval;
    },
    serializeToLEBase256: function() {
        var arr = new Array(8);
        var temp=this.lsw;
        for (var i = 0; i < 4; i++) {
            arr[i] = (temp&255);
            temp=(temp>>8);
        }
        temp = this.msw;
        for (var i = 4; i < 8; i++) {
            arr[i] = (temp&255);
            temp=(temp>>8);
        }
        return arr;
    },
    serializeToLEVar128: function() {
        var arr = new Array(1);
        var temp=this.lsw;
        for (var i = 0; i < 4; i++) {
            arr[i] = (temp&127);
            temp=(temp>>>7);
            if(temp==0&&this.msw==0) return arr;
            arr[i]+=128;
        }        
        arr[4] = (temp&15) | ((this.msw&7)<<4);
        temp=(this.msw>>>3);
        if (temp==0) return arr;
        arr[4]+=128;
        for (var i = 5; i<10; i++) {
            arr[i] = (temp&127);
            temp=(temp>>>7);
            if(temp==0) return arr;
            
            arr[i]+=128;
        }
        return arr;
    },
    unsigned_add:function(other) {
        var temp=this.lsw+other.lsw;
        var local_msw=this.msw+other.msw;
        var local_lsw=temp%4294967296;
        temp-=local_lsw;
        local_msw+=Math.floor(temp/4294967296);
        return new PROTO.I64(local_msw,local_lsw,this.sign);
    },
    sub : function(other) {
        if (other.sign!=this.sign) {
            return this.unsigned_add(other);
        }
        if (other.msw>this.msw || (other.msw==this.msw&&other.lsw>this.lsw)) {
            var retval=other.sub(this);
            retval.sign=-this.sign;
            return retval;
        }
        var local_lsw=this.lsw-other.lsw;
        var local_msw=this.msw-other.msw;       
        if (local_lsw<0) {
            local_lsw+=4294967296;
            local_msw-=1;
        }
        return new PROTO.I64(local_msw,local_lsw,this.sign);        
    },
    /**
     * @param {PROTO.I64} other
     */
    less:function(other){
        if (other.sign!=this.sign) {
            return this.sign<0;
        }
        /**
         * @type {PROTO.I64}
         */
        var a=this;
        /**
         * @type {PROTO.I64}
         */
        var b=other;
        if (this.sign<0) {
            b=this;a=other;
        }
        if (a.msw==b.msw)
            return a.lsw<b.lsw;
        if (a.msw<b.msw)
            return true;
        return false;
    },
    unsigned_less:function(other){
        var a=this,b=other;
        if (a.msw==b.msw)
            return a.lsw<b.lsw;
        if (a.msw<b.msw)
            return true;
        return false;
    },
    add : function(other) {
        if (other.sign<0 && this.sign>=0)
            return this.sub(new PROTO.I64(other.msw,other.lsw,-other.sign));
        if (other.sign>=0 && this.sign<0)
            return other.sub(new PROTO.I64(this.msw,this.lsw,-this.sign));
        return this.unsigned_add(other);
    }
};

PROTO.I64.fromNumber = function(mynum) {
    var sign = (mynum < 0) ? -1 : 1;
    mynum *= sign;
    var lsw = (mynum%4294967296);
    var msw = Math.floor((mynum-lsw)/4294967296);
    return new PROTO.I64(msw, lsw, sign);
};

PROTO.I64.from32pair = function(msw, lsw, sign) {
    return new PROTO.I64(msw, lsw, sign);
};
/**
 * @param {PROTO.Stream} stream
 * @param {PROTO.I64=} float64toassignto
 */
PROTO.I64.parseLEVar128 = function (stream, float64toassignto) {
    var retval = float64toassignto||new PROTO.I64(0,0,1);
    var n = 0;
    var endloop = false;
    var offset=1;
    for (var i = 0; !endloop && i < 5; i++) {
        var byt = stream.readByte();
        if (byt >= 128) {
            byt -= 128;
        } else {
            endloop = true;
        }
        n += offset*byt;
        offset *= 128;
    }
    var lsw=n%4294967296;
    var msw = Math.floor((n - lsw) / 4294967296);   
    offset=8;
    for (var i = 0; !endloop && i < 5; i++) {
        var byt = stream.readByte();
        if (byt >= 128) {
            byt -= 128;
        } else {
            endloop = true;
        }
        msw += offset*byt;
        offset *= 128;
    }
    retval.msw=msw%4294967296;
    retval.lsw=lsw;
    retval.sign=1;
    return retval;
};
/**
 * @param {PROTO.Stream} stream
 * @param {PROTO.I64=} float64toassignto
 */
PROTO.I64.parseLEBase256 = function (stream, float64toassignto) {
    var retval = float64toassignto||new PROTO.I64(0,0,1);
    var n = 0;
    var endloop = false;
    var offset=1;
    for (var i = 0; i < 4; i++) {
        var byt = stream.readByte();
        n += offset*byt;
        offset *= 256;
    }
    var lsw=n;
    var msw=0;
    offset=1;
    for (var i = 0; i < 4; i++) {
        var byt = stream.readByte();
        msw += offset*byt;
        offset *= 256;
    }
    retval.msw=msw;
    retval.lsw=lsw;
    retval.sign=1;
    return retval;
};

PROTO.I64.ONE = new PROTO.I64.fromNumber(1);
PROTO.I64.ZERO = new PROTO.I64.fromNumber(0);

/**
 * + Jonas Raoni Soares Silva
 * http://jsfromhell.com/classes/binary-parser [rev. #1]
 * @constructor
 */ 
PROTO.BinaryParser = function(bigEndian, allowExceptions){
    this.bigEndian = bigEndian, this.allowExceptions = allowExceptions;
};
    PROTO.BinaryParser.prototype.encodeFloat = function(number, precisionBits, exponentBits){
        var n;
        var bias = Math.pow(2, exponentBits - 1) - 1, minExp = -bias + 1, maxExp = bias, minUnnormExp = minExp - precisionBits,
        status = isNaN(n = parseFloat(number)) || n == -Infinity || n == +Infinity ? n : 0,
        exp = 0, len = 2 * bias + 1 + precisionBits + 3, bin = new Array(len),
        signal = (n = status !== 0 ? 0 : n) < 0;
        n = Math.abs(n);
        var intPart = Math.floor(n), floatPart = n - intPart, i, lastBit, rounded, j, result, r;
        for(i = len; i; bin[--i] = 0){}
        for(i = bias + 2; intPart && i; bin[--i] = intPart % 2, intPart = Math.floor(intPart / 2)){}
        for(i = bias + 1; floatPart > 0 && i; (bin[++i] = ((floatPart *= 2) >= 1) - 0) && --floatPart){}
        for(i = -1; ++i < len && !bin[i];){}
        if(bin[(lastBit = precisionBits - 1 + (i = (exp = bias + 1 - i) >= minExp && exp <= maxExp ? i + 1 : bias + 1 - (exp = minExp - 1))) + 1]){
            if(!(rounded = bin[lastBit]))
                for(j = lastBit + 2; !rounded && j < len; rounded = bin[j++]){}
            for(j = lastBit + 1; rounded && --j >= 0; (bin[j] = !bin[j] - 0) && (rounded = 0)){}
        }
        for(i = i - 2 < 0 ? -1 : i - 3; ++i < len && !bin[i];){}

        (exp = bias + 1 - i) >= minExp && exp <= maxExp ? ++i : exp < minExp &&
            (exp != bias + 1 - len && exp < minUnnormExp && this.warn("encodeFloat::float underflow"), i = bias + 1 - (exp = minExp - 1));
        (intPart || status !== 0) && (this.warn(intPart ? "encodeFloat::float overflow" : "encodeFloat::" + status),
            exp = maxExp + 1, i = bias + 2, status == -Infinity ? signal = 1 : isNaN(status) && (bin[i] = 1));
        for(n = Math.abs(exp + bias), j = exponentBits + 1, result = ""; --j; result = (n % 2) + result, n = n >>= 1){}
        for(n = 0, j = 0, i = (result = (signal ? "1" : "0") + result + bin.slice(i, i + precisionBits).join("")).length, r = [];
            i; n += (1 << j) * result.charAt(--i), j == 7 && (r[r.length] = n, n = 0), j = (j + 1) % 8){}
        
        return (this.bigEndian ? r.reverse() : r);
    };
    PROTO.BinaryParser.prototype.encodeInt = function(number, bits, signed){
        var max = Math.pow(2, bits), r = [];
        (number >= max || number < -(max >> 1)) && this.warn("encodeInt::overflow") && (number = 0);
        number < 0 && (number += max);
        for(; number; r[r.length] = number % 256, number = Math.floor(number / 256)){}
        for(bits = -(-bits >> 3) - r.length; bits--;){}
        return (this.bigEndian ? r.reverse() : r);
    };
(function () {
    var buffer8byte = new ArrayBuffer(8);
    var buffer4byte = new ArrayBuffer(4);
    var f64buffer = new DataView(buffer8byte,0,8);
    var f32buffer = new DataView(buffer4byte,0,4);
    var u8buffer64 = new Uint8Array(buffer8byte);
    var u8buffer32 = new Uint8Array(buffer4byte);
    PROTO.BinaryParser.prototype.encodeFloat32 = function(data) {
        f32buffer.setFloat32(0,data,true);
        return u8buffer32;
    }
    PROTO.BinaryParser.prototype.encodeFloat64 = function(data) {
        f64buffer.setFloat64(0,data,true);
        return u8buffer64;
    }
    PROTO.BinaryParser.prototype.decodeFloat32 = function(data) {
        var len=data.length;
        if (len>4) len=4;
        for (var i=0;i<len;++i) {
            u8buffer32[i]=data[i];
        }
        return f32buffer.getFloat32(0,true);
    }
    PROTO.BinaryParser.prototype.decodeFloat64 = function(data) {
        var len=data.length;
        if (len>8) len=8;
        for (var i=0;i<len;++i) {
            u8buffer64[i]=data[i];
        }
        return f64buffer.getFloat64(0,true);
    }
})();
    PROTO.BinaryParser.prototype.decodeFloat = function(data, precisionBits, exponentBits){
        var b = new this.Buffer(this.bigEndian, data);
        PROTO.BinaryParser.prototype.checkBuffer.call(b, precisionBits + exponentBits + 1);
        var bias = Math.pow(2, exponentBits - 1) - 1, signal = PROTO.BinaryParser.prototype.readBits.call(b,precisionBits + exponentBits, 1);
        var exponent = PROTO.BinaryParser.prototype.readBits.call(b,precisionBits, exponentBits), significand = 0;
        var divisor = 2;
        var curByte = b.buffer.length + (-precisionBits >> 3) - 1;
        var byteValue, startBit, mask;
        do
            for(byteValue = b.buffer[ ++curByte ], startBit = precisionBits % 8 || 8, mask = 1 << startBit;
                mask >>= 1; (byteValue & mask) && (significand += 1 / divisor), divisor *= 2){}
        while((precisionBits -= startBit));
        return exponent == (bias << 1) + 1 ? significand ? NaN : signal ? -Infinity : +Infinity
            : (1 + signal * -2) * (exponent || significand ? !exponent ? Math.pow(2, -bias + 1) * significand
            : Math.pow(2, exponent - bias) * (1 + significand) : 0);
    };
    PROTO.BinaryParser.prototype.decodeInt = function(data, bits, signed){
        var b = new this.Buffer(this.bigEndian, data), x = b.readBits(0, bits), max = Math.pow(2, bits);
        return signed && x >= max / 2 ? x - max : x;
    };
    PROTO.BinaryParser.prototype.Buffer = function(bigEndian, buffer){
        this.bigEndian = bigEndian || 0;
        this.buffer = [];
        PROTO.BinaryParser.prototype.setBuffer.call(this,buffer);
    };

        PROTO.BinaryParser.prototype.readBits = function(start, length){
            //shl fix: Henri Torgemane ~1996 (compressed by Jonas Raoni)
            function shl(a, b){
                for(++b; --b; a = ((a %= 0x7fffffff + 1) & 0x40000000) == 0x40000000 ? a * 2 : (a - 0x40000000) * 2 + 0x7fffffff + 1){}
                return a;
            }
            if(start < 0 || length <= 0)
                return 0;
            PROTO.BinaryParser.prototype.checkBuffer.call(this, start + length);
            for(var offsetLeft, offsetRight = start % 8, curByte = this.buffer.length - (start >> 3) - 1,
                lastByte = this.buffer.length + (-(start + length) >> 3), diff = curByte - lastByte,
                sum = ((this.buffer[ curByte ] >> offsetRight) & ((1 << (diff ? 8 - offsetRight : length)) - 1))
                + (diff && (offsetLeft = (start + length) % 8) ? (this.buffer[ lastByte++ ] & ((1 << offsetLeft) - 1))
                << (diff-- << 3) - offsetRight : 0); diff; sum += shl(this.buffer[ lastByte++ ], (diff-- << 3) - offsetRight)
                ){}
            return sum;
        };
        PROTO.BinaryParser.prototype.setBuffer = function(data){
            if(data){
                for(var l, i = l = data.length, b = this.buffer = new Array(l); i; b[l - i] = data[--i]){}
                this.bigEndian && b.reverse();
            }
        };
        PROTO.BinaryParser.prototype.hasNeededBits = function(neededBits){
            return this.buffer.length >= -(-neededBits >> 3);
        };
        PROTO.BinaryParser.prototype.checkBuffer = function(neededBits){
            if(!PROTO.BinaryParser.prototype.hasNeededBits.call(this,neededBits))
                throw new Error("checkBuffer::missing bytes");
        };
    
    PROTO.BinaryParser.prototype.warn = function(msg){
        if(this.allowExceptions)
            throw new Error(msg);
        return 1;
    };

    PROTO.BinaryParser.prototype.toSmall = function(data){return this.decodeInt(data, 8, true);};
    PROTO.BinaryParser.prototype.fromSmall = function(number){return this.encodeInt(number, 8, true);};
    PROTO.BinaryParser.prototype.toByte = function(data){return this.decodeInt(data, 8, false);};
    PROTO.BinaryParser.prototype.fromByte = function(number){return this.encodeInt(number, 8, false);};
    PROTO.BinaryParser.prototype.toShort = function(data){return this.decodeInt(data, 16, true);};
    PROTO.BinaryParser.prototype.fromShort = function(number){return this.encodeInt(number, 16, true);};
    PROTO.BinaryParser.prototype.toWord = function(data){return this.decodeInt(data, 16, false);};
    PROTO.BinaryParser.prototype.fromWord = function(number){return this.encodeInt(number, 16, false);};
    PROTO.BinaryParser.prototype.toInt = function(data){return this.decodeInt(data, 32, true);};
    PROTO.BinaryParser.prototype.fromInt = function(number){return this.encodeInt(number, 32, true);};
    PROTO.BinaryParser.prototype.toDWord = function(data){return this.decodeInt(data, 32, false);};
    PROTO.BinaryParser.prototype.fromDWord = function(number){return this.encodeInt(number, 32, false);};
    PROTO.BinaryParser.prototype.toFloat = typeof(Float32Array) != "undefined"?PROTO.BinaryParser.prototype.decodeFloat32:function(data){return this.decodeFloat(data, 23, 8);};
    PROTO.BinaryParser.prototype.fromFloat = typeof(Float32Array) != "undefined"?PROTO.BinaryParser.prototype.encodeFloat32:function(number){return this.encodeFloat(number, 23, 8);};
    PROTO.BinaryParser.prototype.toDouble = typeof(Float64Array) != "undefined"?PROTO.BinaryParser.prototype.decodeFloat64:function(data){return this.decodeFloat(data, 52, 11);};
    PROTO.BinaryParser.prototype.fromDouble = typeof(Float64Array) != "undefined"?PROTO.BinaryParser.prototype.encodeFloat64:function(number){return this.encodeFloat(number, 52, 11);};

PROTO.binaryParser = new PROTO.BinaryParser(false,false);


PROTO.encodeUTF8 = function(str) {
    var strlen = str.length;
    var u8 = [];
    var c, nextc;
    var x, y, z;
    for (var i = 0; i < strlen; i++) {
        c = str.charCodeAt(i);
        if ((c & 0xff80) == 0) {
            // ASCII
            u8.push(c);
        } else {
            if ((c & 0xfc00) == 0xD800) {
                nextc = str.charCodeAt(i+1);
                if ((nextc & 0xfc00) == 0xDC00) {
                    // UTF-16 Surrogate pair
                    c = (((c & 0x03ff)<<10) | (nextc & 0x3ff)) + 0x10000;
                    i++;
                } else {
                    // error.
                    PROTO.warn("Error decoding surrogate pair: "+c+"; "+nextc);
                }
            }
            x = c&0xff;
            y = c&0xff00;
            z = c&0xff0000;
            // Encode UCS code into UTF-8
            if (c <= 0x0007ff) {
                u8.push(0xc0 | (y>>6) | (x>>6));
                u8.push(0x80 | (x&63));
            } else if (c <= 0x00ffff) {
                u8.push(0xe0 | (y>>12));
                u8.push(0x80 | ((y>>6)&63) | (x>>6));
                u8.push(0x80 | (x&63));
            } else if (c <= 0x10ffff) {
                u8.push(0xf0 | (z>>18));
                u8.push(0x80 | ((z>>12)&63) | (y>>12));
                u8.push(0x80 | ((y>>6)&63) | (x>>6));
                u8.push(0x80 | (x&63));
            } else {
                // error.
                PROTO.warn("Error encoding to utf8: "+c+" is greater than U+10ffff");
                u8.push("?".charCodeAt(0));
            }
        }
    }
    return u8;
}

PROTO.decodeUTF8 = function(u8) {
    var u8len = u8.length;
    var str = "";
    var c, b2, b3, b4;
    for (var i = 0; i < u8len; i++) {
        c = u8[i];
        if ((c&0x80) == 0x00) {
        } else if ((c&0xf8) == 0xf0) {
            // 4 bytes: U+10000 - U+10FFFF
            b2 = u8[i+1];
            b3 = u8[i+2];
            b4 = u8[i+3];
            if ((b2&0xc0) == 0x80 && (b3&0xc0) == 0x80 && (b4&0xc0) == 0x80) {
                c = (c&7)<<18 | (b2&63)<<12 | (b3&63)<<6 | (b4&63);
                i+=3;
            } else {
                // error.
                PROTO.warn("Error decoding from utf8: "+c+","+b2+","+b3+","+b4);
                continue;
            }
        } else if ((c&0xf0)==0xe0) {
            // 3 bytes: U+0800 - U+FFFF
            b2 = u8[i+1];
            b3 = u8[i+2];
            if ((b2&0xc0) == 0x80 && (b3&0xc0) == 0x80) {
                c = (c&15)<<12 | (b2&63)<<6 | (b3&63);
                i+=2;
            } else {
                // error.
                PROTO.warn("Error decoding from utf8: "+c+","+b2+","+b3);
                continue;
            }
        } else if ((c&0xe0)==0xc0) {
            // 2 bytes: U+0080 - U+07FF
            b2 = u8[i+1];
            if ((b2&0xc0) == 0x80) {
                c = (c&31)<<6 | (b2&63);
                i+=1;
            } else {
                // error.
                PROTO.warn("Error decoding from utf8: "+c+","+b2);
                continue;
            }
        } else {
            // error.
            // 80-BF: Second, third, or fourth byte of a multi-byte sequence
            // F5-FF: Start of 4, 5, or 6 byte sequence
            PROTO.warn("Error decoding from utf8: "+c+" encountered not in multi-byte sequence");
            continue;
        }
        if (c <= 0xffff) {
            str += String.fromCharCode(c);
        } else if (c > 0xffff && c <= 0x10ffff) {
            // Must be encoded into UTF-16 surrogate pair.
            c -= 0x10000;
            str += (String.fromCharCode(0xD800 | (c>>10)) + String.fromCharCode(0xDC00 | (c&1023)));
        } else {
            PROTO.warn("Error encoding surrogate pair: "+c+" is greater than U+10ffff");
        }
    }
    return str;
}


/**
 * @constructor
 */
PROTO.Stream = function () {
    this.write_pos_ = 0;
    this.read_pos_ = 0;
};
PROTO.Stream.prototype = {
    read: function(amt) {
        var result = [];
        for (var i = 0; i < amt; ++i) {
            var byt = this.readByte();
            if (byt === null) {
                break;
            }
            result.push(byt);
        }
        return result;
    },
    write: function(array) {
        for (var i = 0; i < array.length; i++) {
            this.writeByte(array[i]);
        }
    },
    readByte: function() {
        return null;
    },
    writeByte: function(byt) {
        this.write_pos_ += 1;
    },
    valid: function() {
        return false;
    }
};
/**
 * @constructor
 * @extends {PROTO.Stream}
 * @param {Array=} arr  Existing byte array to read from, or append to.
 */
PROTO.ByteArrayStream = function(arr) {
    this.array_ = arr || new Array();
    this.read_pos_ = 0;
    this.write_pos_ = this.array_.length;
};
PROTO.ByteArrayStream.prototype = new PROTO.Stream();
PROTO.ByteArrayStream.prototype.read = function(amt) {
    if (this.read_pos_+amt > this.array_.length) {
        // incomplete stream.
        //throw new Error("Read past end of protobuf ByteArrayStream: "+
        //                this.array_.length+" < "+this.read_pos_+amt);
        return null;
    }
    var ret = this.array_.slice(this.read_pos_, this.read_pos_+amt);
    this.read_pos_ += amt;
    return ret;
};
PROTO.ByteArrayStream.prototype.write = function(arr) {
    Array.prototype.push.apply(this.array_, arr);
    this.write_pos_ = this.array_.length;
};
PROTO.ByteArrayStream.prototype.readByte = function() {
    return this.array_[this.read_pos_ ++];
};
PROTO.ByteArrayStream.prototype.writeByte = function(byt) {
    this.array_.push(byt);
    this.write_pos_ = this.array_.length;
};
PROTO.ByteArrayStream.prototype.valid = function() {
    return this.read_pos_ < this.array_.length;
};
PROTO.ByteArrayStream.prototype.getArray = function() {
    return this.array_;
};
/**
 * @constructor
 */
PROTO.Uint8ArrayStream = function(arr) {
    this.array_ = arr || new Uint8Array(4096);
    this.read_pos_ = 0;
    this.write_pos_ = 0;
}
PROTO.Uint8ArrayStream.prototype._realloc = function(new_size) {
    this.array_ = new Uint8Array(Math.max(new_size, this.array_.length)
				 + this.array_.length);
}
PROTO.Uint8ArrayStream.prototype.read = function(amt) {
    if (this.read_pos_+amt > this.array_.length) {
        return null;
    }
    var ret = this.array_.subarray(this.read_pos_, this.read_pos_+amt);
    this.read_pos_ += amt;
    return ret;
};
PROTO.Uint8ArrayStream.prototype.write = function(arr) {
    if (this.write_pos_ + arr.length > this.array_.length) {
	this._realloc(this.write_pos_ + arr.length);
    }
    this.array_.set(arr, this.write_pos_);
    this.write_pos_ += arr.length;
};
PROTO.Uint8ArrayStream.prototype.readByte = function() {
    return this.array_[this.read_pos_ ++];
};
PROTO.Uint8ArrayStream.prototype.writeByte = function(byt) {
    if (this.write_pos_ >= this.array_.length) {
	this._realloc(this.write_pos_ + 1);
    }
    this.array_[this.write_pos_++] = byt;
};
PROTO.Uint8ArrayStream.prototype.valid = function() {
    return this.read_pos_ < this.array_.length;
};
PROTO.Uint8ArrayStream.prototype.getArray = function() {
    return this.array_.subarray(0, this.write_pos_);
};

PROTO.CreateArrayStream = function(arr) {
  if (arr instanceof Array) {
    return new PROTO.ByteArrayStream(arr);
  } else {
    return new PROTO.Uint8ArrayStream(arr);
  }
};

(function(){
    var FromB64AlphaMinus43=[
        62,-1,62,-1,63,52,53,54,55,56,57,58,59,60,61,
        -1,-1,-1,-1,-1,-1,-1,
        0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,
        17,18,19,20,21,22,23,24,25,
        -1,-1,-1,-1,63,-1,
        26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,
        41,42,43,44,45,46,47,48,49,50,51];
    var ToB64Alpha=[
        'A','B','C','D','E','F','G','H','I','J','K','L','M',
        'N','O','P','Q','R','S','T','U','V','W','X','Y','Z',
        'a','b','c','d','e','f','g','h','i','j','k','l','m',
        'n','o','p','q','r','s','t','u','v','w','x','y','z',
        '0','1','2','3','4','5','6','7','8','9','+','/'];
    var ToB64Alpha_URLSafe=[
        'A','B','C','D','E','F','G','H','I','J','K','L','M',
        'N','O','P','Q','R','S','T','U','V','W','X','Y','Z',
        'a','b','c','d','e','f','g','h','i','j','k','l','m',
        'n','o','p','q','r','s','t','u','v','w','x','y','z',
        '0','1','2','3','4','5','6','7','8','9','-','_'];
     /**
      * @constructor
      * @extends {PROTO.Stream}
      * @param {string=} b64string  String to read from, or append to.
      */
    PROTO.Base64Stream = function(b64string) {
        this.alphabet = ToB64Alpha;
        this.string_ = b64string || '';
        this.read_pos_ = 0;
        this.read_incomplete_value_ = 0;
        this.read_needed_bits_ = 8;
        this.write_extra_bits_ = 0;
        this.write_incomplete_value_ = 0;
        this.fixString();
    };
    PROTO.Base64Stream.prototype = new PROTO.Stream();
    PROTO.Base64Stream.prototype.setURLSafe = function() {
        this.alphabet = ToB64Alpha_URLSafe;
    };
    PROTO.Base64Stream.prototype.fixString = function() {
        var len = this.string_.length;
        if (this.string_[len-1]=='=') {
            var n = 4;
            var cutoff = 2;
            if (this.string_[len-cutoff]=='=') {
                n = 2;
                cutoff = 3;
            }
            this.write_extra_bits_ = n;
            this.write_incomplete_value_ = FromB64AlphaMinus43[
                this.string_.charCodeAt(len-cutoff)-43];
            this.write_incomplete_value_ >>= (6-n);
            this.string_ = this.string_.substring(0,len-cutoff);
        }
    };
    PROTO.Base64Stream.prototype.readByte = function() {
        var next6bits;
        var n = this.read_needed_bits_;
        while (next6bits === undefined || next6bits == -1) {
            if (this.read_pos_ >= this.string_.length) {
                if (this.valid()) {
                    next6bits = this.write_incomplete_value_ << (6-n);
                    this.read_pos_++;
                    break;
                } else {
                    return null;
                }
            }
            next6bits = FromB64AlphaMinus43[
                this.string_.charCodeAt(this.read_pos_++)-43];
        }
        if (n == 8) {
            this.read_incomplete_value_ = next6bits;
            this.read_needed_bits_ = 2;
            return this.readByte();
        }
        var ret = this.read_incomplete_value_<<n;
        ret |= next6bits>>(6-n);
        this.read_incomplete_value_ = next6bits&((1<<(6-n))-1);
        this.read_needed_bits_ += 2;
        return ret;
    };

    PROTO.Base64Stream.prototype.writeByte = function(byt) {
        this.write_extra_bits_ += 2;
        var n = this.write_extra_bits_;
        this.string_ += this.alphabet[
                byt>>n | this.write_incomplete_value_<<(8-n)];
        this.write_incomplete_value_ = (byt&((1<<n)-1));
        if (n == 6) {
            this.string_ += this.alphabet[this.write_incomplete_value_];
            this.write_extra_bits_ = 0;
            this.write_incomplete_value_ = 0;
        }
        if (this.string_.length%77==76) {
            this.string_ += "\n";
        }
    };

    PROTO.Base64Stream.prototype.getString = function() {
        var len = this.string_.length;
        var retstr = this.string_;
        var n = this.write_extra_bits_;
        if (n > 0) {
            retstr += this.alphabet[this.write_incomplete_value_<<(6-n)];
            if (n==2) {
                retstr += "==";
            } else if (n==4) {
                retstr += "=";
            }
        }
        return retstr;
    };
    PROTO.Base64Stream.prototype.valid = function() {
        return (this.read_pos_ < this.string_.length) ||
               (this.read_pos_==this.string_.length && this.write_extra_bits_);
    };
})();

if (typeof(ArrayBuffer) !== "undefined" && typeof(Uint8Array) !== "undefined") {
    /**
     * @constructor
     * @extends {PROTO.Stream}
     * @param {Array|ArrayBuffer|TypedArray} arr
     * @param {number=} length
     */
    PROTO.ArrayBufferStream = function(arr, length) {
	this.array_buffer_ = arr || new ArrayBuffer(1024);
	this.length_ = length || 0;
	this.array_ = new Uint8Array(this.array_buffer_);
	this.read_pos = 0;
    };
    PROTO.ArrayBufferStream.prototype = new PROTO.Stream();
    PROTO.ArrayBufferStream.prototype._realloc = function(min_length) {
	var old_array = this.array_;
	var length = this.length_;
	var new_buf_length = old_array.length + min_length;
	this.array_buffer_ = new ArrayBuffer(new_buf_length);
	var new_array = new Uint8Array(this.array_buffer_);
	for (var i = 0; i < length; i++) {
	    new_array[i] = old_array[i];
	}
	this.array_ = new_array;
    };
    PROTO.ArrayBufferStream.prototype.read = function(amt) {
	if (this.read_pos_+amt > this.length_) {
	    // incomplete stream.
	    //throw new Error("Read past end of protobuf ArrayBufferStream: "+
	    //                this.array_.length+" < "+this.read_pos_+amt);
	    return null;
	}
	var ret = this.array_.subarray(this.read_pos_, this.read_pos_+amt);
	this.read_pos_ += amt;
	// FIXME
	var ret_as_array = new Array(amt);
	for (var i = 0; i < amt; i++) {
	    ret_as_array[i] = ret[i];
	}
	return ret_as_array;
    };
    PROTO.ArrayBufferStream.prototype.write = function(arr) {
	var si = 0;
	var di = this.length_;
	if (this.length_ + arr.length > this.array_.length) {
	    this._realloc(this.length_ + arr.length);
	}
	this.length_ += arr.length;
	var dest = this.array_;
	var len = arr.length;
	for (;si < len; si++,di++) {
	    dest[di] = arr[si];
	}
    };
    PROTO.ArrayBufferStream.prototype.readByte = function() {
	return this.array_[this.read_pos_ ++];
    };
    PROTO.ArrayBufferStream.prototype.writeByte = function(byt) {
	if (this.length_ == this.array_.length) {
	    this._realloc(this.length_ + 1);
	}
	this.array_[this.length_ ++] = byt;
    };
    PROTO.ArrayBufferStream.prototype.valid = function() {
	return this.read_pos_ < this.length_;
    };
    PROTO.ArrayBufferStream.prototype.getArrayBuffer = function() {
	return this.array_buffer_;
    };
    PROTO.ArrayBufferStream.prototype.length = function() {
	return this.length_;
    };
    (function() {
	var useBlobCons = false;
	var BlobBuilder = null;
	var slice = "slice";
	var testBlob;
	try {
	    testBlob = new self.Blob([new ArrayBuffer(1)]);
	    useBlobCons = true;
	} catch (e) {
        /**
         * @suppress {missingProperties} self
         */
	    BlobBuilder = self.BlobBuilder || 
            self["WebKitBlobBuilder"] || self["MozBlobBuilder"] || self["MSBlobBuilder"];
        try {
	        testBlob = new BlobBuilder().getBlob();
        }catch (f) {
            //in a worker in FF or blobs not supported
        }
	}
	if (testBlob && (useBlobCons || BlobBuilder)) {
	    if (testBlob.webkitSlice) {
		slice = "webkitSlice";
	    }
	    if (testBlob.mozSlice) {
		slice = "mozSlice";
	    }
	    PROTO.ArrayBufferStream.prototype.getBlob = function() {
		var fullBlob;
		if (useBlobCons) {
		    fullBlob = new self.Blob([this.array_buffer_]);
		} else {
		    var blobBuilder = new BlobBuilder();
		    blobBuilder.append(this.array_buffer_);
		    fullBlob = blobBuilder.getBlob();
		}
		return fullBlob[slice](0, this.length_);
	    };
	}
    }());
    PROTO.ArrayBufferStream.prototype.getUint8Array = function() {
	return new Uint8Array(this.array_buffer_, 0, this.length_);
    };
}

PROTO.array =
    (function() {
        /** @constructor */
        function ProtoArray(datatype, input) {
            this.datatype_ = datatype.type();
            this.length = 0;
            if (PROTO.IsArray(input)) {
                for (var i=0;i<input.length;++i) {
                    this.push(input[i]);
                }
            }
        };
        ProtoArray.IsInitialized = function IsInitialized(val) {
            return val.length > 0;
        };
        ProtoArray.prototype = {};
        ProtoArray.prototype.push = function (var_args) {
            if (arguments.length === 0) {
                if (this.datatype_.composite) {
                    var newval = new this.datatype_;
                    this[this.length++] = newval;
                    return newval;
                } else {
                    throw "Called add(undefined) for a non-composite";
                }
            } else {
                for (var i = 0; i < arguments.length; i++) {
                    var newval = this.datatype_.Convert(arguments[i]);
                    if (this.datatype_.FromProto) {
                        newval = this.datatype_.FromProto(newval);
                    }
                    this[this.length++] = newval;
                }
            }
            return arguments[0];
        }
        ProtoArray.prototype.set = function (index, newval) {
            newval = this.datatype_.Convert(newval);
            if (this.datatype_.FromProto) {
                newval = this.datatype_.FromProto(newval);
            }
            if (index < this.length && index >= 0) {
                this[index] = newval;
            } else if (index == this.length) {
                this[this.length++] = newval;
            } else {
                throw "Called ProtoArray.set with index "+index+" higher than length "+this.length;
            }
            return newval;
        }
        ProtoArray.prototype.clear = function (index, newval) {
            this.length = 0;
        }
        return ProtoArray;
    })();

PROTO.string = {
    Convert: function(str) {
        return ''+str;
    },
    wiretype: PROTO.wiretypes.lengthdelim,
    SerializeToStream: function(str, stream) {
        var arr = PROTO.encodeUTF8(str);
        return PROTO.bytes.SerializeToStream(arr, stream);
    },
    ParseFromStream: function(stream) {
        var arr = PROTO.bytes.ParseFromStream(stream);
        return PROTO.decodeUTF8(arr);
    },
    toString: function(str) {return str;}
};

PROTO.bytes = {
    Convert: function(arr) {
        if (PROTO.IsArray(arr)) {
            return arr;
        } else if (arr instanceof PROTO.ByteArrayStream) {
            return arr.getArray();
        } else if (arr.SerializeToStream) {
            /* This is useful for messages (e.g. RPC calls) that embed
             * other messages inside them using the bytes type.
             */
            // FIXME: should we always allow this? Can this cause mistakes?
            var tempStream = new PROTO.ByteArrayStream;
            arr.SerializeToStream(tempStream);
            return tempStream.getArray();
        } else {
            throw "Not a Byte Array: "+arr;
        }
    },
    wiretype: PROTO.wiretypes.lengthdelim,
    SerializeToStream: function(arr, stream) {
        PROTO.int32.SerializeToStream(arr.length, stream);
        stream.write(arr);
    },
    ParseFromStream: function(stream) {
        var len = PROTO.int32.ParseFromStream(stream);
        return stream.read(len);
    },
    toString: function(bytes) {return '['+bytes+']';}
};

(function() {
    function makeclass(converter, serializer, parser) {
        var myclass = {
            Convert: converter,
            wiretype: 0,
            SerializeToStream: serializer,
            ParseFromStream: parser,
            toString: function(val) {return "" + val}
        };
        return myclass;
    };
    function convertU32(n) { //unsigned
        if (n == NaN) {
            throw "not a number: "+n;
        }
        n = Math.round(n);
        if (n < 0) {
            throw "uint32/fixed32 does not allow negative: "+n;
        }
        if (n > 4294967295) {
            throw "uint32/fixed32 out of bounds: "+n;
        }
        return n;
    };
    function convertS32(n) { // signed
        if (n == NaN) {
            throw "not a number: "+n;
        }
        n = Math.round(n);
        if (n > 2147483647 || n < -2147483648) {
            throw "sfixed32/[s]int32 out of bounds: "+n;
        }
        return n;
    };
    function serializeFixed32(n, stream) {
        if (n<0) n += 4294967296;
        var arr = new Array(4);
        for (var i = 0; i < 4; i++) {
            arr[i] = n%256;
            n >>>= 8;
        }
        stream.write(arr);
    };
    function parseSFixed32(stream) {
        var n = 0;
        var offset=1;
        for (var i = 0; i < 4; i++) {
            n += offset*stream.readByte();
            offset *= 256;
        }
        return n;
    };
    function parseFixed32(stream) {
        var n = parseSFixed32(stream);
        if (n > 2147483647) {
            n -= 4294967296;
        }
        return n;
    };
    function serializeInt32(n, stream) {
        if (n < 0) {
            serializeInt64(PROTO.I64.fromNumber(n),stream);
            return;
        }
        // Loop once regardless of whether n is 0.
        for (var i = 0; i==0 || (n && i < 5); i++) {
            var byt = n%128;
            n >>>= 7;
            if (n) {
                byt += 128;
            }
            stream.writeByte(byt);
        }
    };
    function serializeSInt32(n, stream) {
        if (n < 0) {
            n = -n*2-1;
        } else {
            n = n*2;
        }
        serializeInt32(n, stream);
    };
    function parseUInt32(stream) {
        var n = 0;
        var endloop = false;
        var offset=1;
        for (var i = 0; !endloop && i < 5; i++) {
            var byt = stream.readByte();
            if (byt === undefined) {
                PROTO.warn("read undefined byte from stream: n is "+n);
                break;
            }
            if (byt < 128) {
                endloop = true;
            }
            n += offset*(byt&(i==4?15:127));
            offset *= 128;
        }
        return n;
    };
    var temp64num = new PROTO.I64(0,0,1);
    function parseInt32(stream) {
        var n = PROTO.I64.parseLEVar128(stream,temp64num);
        var lsw=n.lsw;
        if (lsw > 2147483647) {
            lsw -= 2147483647;
            lsw -= 2147483647;
            lsw -= 2;
        }
        return lsw;
    };
    function parseSInt32(stream) {
        var n = parseUInt32(stream);
        if (n & 1) {
            return (n+1) / -2;
        }
        return n / 2;
    }
    PROTO.sfixed32 = makeclass(convertS32, serializeFixed32, parseSFixed32);
    PROTO.fixed32 = makeclass(convertU32, serializeFixed32, parseFixed32);
    PROTO.sfixed32.wiretype = PROTO.wiretypes.fixed32;
    PROTO.fixed32.wiretype = PROTO.wiretypes.fixed32;
    PROTO.int32 = makeclass(convertS32, serializeInt32, parseInt32);
    PROTO.sint32 = makeclass(convertS32, serializeSInt32, parseSInt32);
    PROTO.uint32 = makeclass(convertU32, serializeInt32, parseUInt32);

    function convert64(n) {
        if (n instanceof PROTO.I64) {
            return n;
        }
        throw "64-bit integers must be PROTO.I64 objects!";
    };
    function serializeInt64(n, stream) {
        stream.write(n.convertToUnsigned().serializeToLEVar128());
    }
    function serializeSInt64(n, stream) {
        stream.write(n.convertFromUnsigned().convertToZigzag().serializeToLEVar128());
    }
    function serializeUInt64(n, stream) {
        stream.write(n.convertToUnsigned().serializeToLEVar128());
    }
    function serializeSFixed64(n, stream) {
        stream.write(n.convertToUnsigned().serializeToLEBase256());
    }
    function serializeFixed64(n, stream) {
        stream.write(n.serializeToLEBase256());
    }
    function parseSFixed64(stream) {
        return PROTO.I64.parseLEBase256(stream,temp64num).convertFromUnsigned();
    }
    function parseFixed64(stream) {
        return PROTO.I64.parseLEBase256(stream);
    }
    function parseSInt64(stream) {
        return PROTO.I64.parseLEVar128(stream,temp64num).convertFromZigzag();
    }
    function parseInt64(stream) {
        return PROTO.I64.parseLEVar128(stream,temp64num).convertFromUnsigned();
    }
    function parseUInt64(stream) {
        return PROTO.I64.parseLEVar128(stream);
    }
    PROTO.sfixed64 = makeclass(convert64, serializeSFixed64, parseSFixed64);
    PROTO.fixed64 = makeclass(convert64, serializeFixed64, parseFixed64);
    PROTO.sfixed64.wiretype = PROTO.wiretypes.fixed64;
    PROTO.fixed64.wiretype = PROTO.wiretypes.fixed64;
    PROTO.int64 = makeclass(convert64, serializeInt64, parseInt64);
    PROTO.sint64 = makeclass(convert64, serializeSInt64, parseSInt64);
    PROTO.uint64 = makeclass(convert64, serializeUInt64, parseUInt64);

    PROTO.bool = makeclass(function(bool) {return bool?true:false;},
                           serializeInt32,
                           parseUInt32);

    function convertFloatingPoint(f) {
        var n = parseFloat(f);
        if (n == NaN) {
            throw "not a number: "+f;
        }
        return n;
    };
    function writeFloat(flt, stream) {
        stream.write(PROTO.binaryParser.fromFloat(flt));
    };
    function readFloat(stream) {
        var arr = stream.read(4);
        return PROTO.binaryParser.toFloat(arr);
    };
    function writeDouble(flt, stream) {
        stream.write(PROTO.binaryParser.fromDouble(flt));
    };
    function readDouble(stream) {
        var arr = stream.read(8);
        return PROTO.binaryParser.toDouble(arr);
    };
    PROTO.Float = makeclass(convertFloatingPoint, writeFloat, readFloat);
    PROTO.Double = makeclass(convertFloatingPoint, writeDouble, readDouble);
    PROTO.Float.wiretype = PROTO.wiretypes.fixed32;
    PROTO.Double.wiretype = PROTO.wiretypes.fixed64;
})();


PROTO.mergeProperties = function(properties, stream, values) {
    var fidToProp = {};
    for (var key in properties) {
        fidToProp[properties[key].id] = key;
    }
    var nextfid, nexttype, nextprop, nextproptype, nextval, nextpropname;
    var incompleteTuples = {};
    while (stream.valid()) {
        nextfid = PROTO.int32.ParseFromStream(stream);
//        PROTO.warn(""+stream.read_pos_+" ; "+stream.array_.length);
        nexttype = nextfid % 8;
        nextfid >>>= 3;
        nextpropname = fidToProp[nextfid];
        nextprop = nextpropname && properties[nextpropname];
        nextproptype = nextprop && nextprop.type();
        nextval = undefined;
        switch (nexttype) {
        case PROTO.wiretypes.varint:
//        PROTO.warn("read varint field is "+nextfid);
            if (nextprop && nextproptype.wiretype == PROTO.wiretypes.varint) {
                nextval = nextproptype.ParseFromStream(stream);
            } else {
                PROTO.int64.ParseFromStream(stream);
            }
            break;
        case PROTO.wiretypes.fixed64:
//        PROTO.warn("read fixed64 field is "+nextfid);
            if (nextprop && nextproptype.wiretype == PROTO.wiretypes.fixed64) {
                nextval = nextproptype.ParseFromStream(stream);
            } else {
                PROTO.fixed64.ParseFromStream(stream);
            }
            break;
        case PROTO.wiretypes.lengthdelim:
//        PROTO.warn("read lengthdelim field is "+nextfid);
            if (nextprop) {
                if (nextproptype.wiretype != PROTO.wiretypes.lengthdelim)
                {
                    var tup;
                    if (nextproptype.cardinality>1) {
                        if (incompleteTuples[nextpropname]===undefined) {
                            incompleteTuples[nextpropname]=new Array();
                        }
                        tup = incompleteTuples[nextpropname];
                    }
                    var bytearr = PROTO.bytes.ParseFromStream(stream);
                    var bas = PROTO.CreateArrayStream(bytearr);
                    for (var j = 0; j < bytearr.length && bas.valid(); j++) {
                        var toappend = nextproptype.ParseFromStream(bas);

                        if (nextproptype.cardinality>1) {
                            tup.push(toappend);
                            if (tup.length==nextproptype.cardinality) {
                                if (nextprop.multiplicity == PROTO.repeated) {
                                    values[nextpropname].push(tup);
                                } else {
                                    values[nextpropname] =
                                        nextproptype.Convert(tup);
                                }
                                incompleteTuples[nextpropname]=new Array();
                                tup = incompleteTuples[nextpropname];
                            }
                        }else {
                            values[nextpropname].push(toappend);
                        }
                    }
                } else {
                    nextval = nextproptype.ParseFromStream(stream);
                    if (nextval == null) {
                        return false;
                    }
                }
            } else {
                PROTO.bytes.ParseFromStream(stream);
            }
            break;
        case PROTO.wiretypes.fixed32:
//        PROTO.warn("read fixed32 field is "+nextfid);
            if (nextprop && nextproptype.wiretype == PROTO.wiretypes.fixed32) {
                nextval = nextproptype.ParseFromStream(stream);
            } else {
                PROTO.fixed32.ParseFromStream(stream);
            }
            break;
        default:
            PROTO.warn("ERROR: Unknown type "+nexttype+" for "+nextfid);
            break;
        }
        if (nextval !== undefined) {
            if (values[nextpropname] === undefined && nextproptype.cardinality>1) {
                values[nextpropname] = {};
            }
            if (nextproptype.cardinality>1) {
                var tup;
                if (incompleteTuples[nextpropname]===undefined) {
                    incompleteTuples[nextpropname]=new Array();
                    tup = incompleteTuples[nextpropname];
                }
                tup.push(nextval);
                if (tup.length==nextproptype.cardinality) {
                    if (nextprop.multiplicity == PROTO.repeated) {
                        values[nextpropname].push(tup);
                    } else {
                        tup = nextproptype.Convert(tup);
                        if (!PROTO.DefineProperty && nextproptype.FromProto) {
                            tup = nextproptype.FromProto(tup);
                        }
                        values[nextpropname] = tup;
                    }
                    incompleteTuples[nextpropname] = undefined;
                }
            } else if (nextprop.multiplicity === PROTO.repeated) {
                values[nextpropname].push(nextval);
            } else {
                nextval = nextproptype.Convert(nextval);
                if (!PROTO.DefineProperty && nextproptype.FromProto) {
                    nextval = nextproptype.FromProto(nextval);
                }
                values[nextpropname] = nextval;
            }
        }
    }
    return true;
};

/*
    var str = '{';
    for (var key in property) {
        str+=key+': '+property[key]+', ';
    }
    str+='}';
    throw str;
*/

PROTO.serializeTupleProperty = function(property, stream, value) {
    var fid = property.id;
    var wiretype = property.type().wiretype;
    var wireId = fid * 8 + wiretype;
//    PROTO.warn("Serializing property "+fid+" as "+wiretype+" pos is "+stream.write_pos_);
    if (wiretype != PROTO.wiretypes.lengthdelim && property.options.packed) {
        var bytearr = new Array();
        // Don't know length beforehand.
        var bas = new PROTO.ByteArrayStream(bytearr);
        if (property.multiplicity == PROTO.repeated) {
            for (var i = 0; i < value.length; i++) {
                var val = property.type().Convert(value[i]);
                for (var j=0;j<property.type().cardinality;++j) {
                    property.type().SerializeToStream(val[j], bas);
                }
            }
        }else {
            var val = property.type().Convert(value);
            for (var j=0;j<property.type().cardinality;++j) {
                property.type().SerializeToStream(val[j], bas);
            }
        }
        wireId = fid * 8 + PROTO.wiretypes.lengthdelim;
        PROTO.int32.SerializeToStream(wireId, stream);
        PROTO.bytes.SerializeToStream(bytearr, stream);
    } else {
        if (property.multiplicity == PROTO.repeated) {
            for (var i = 0; i < value.length; i++) {
                var val = property.type().Convert(value[i]);
                for (var j=0;j<property.type().cardinality;++j) {
                    PROTO.int32.SerializeToStream(wireId, stream);
                    property.type().SerializeToStream(val[j], stream);
                }
            }
        }else {
            var val = property.type().Convert(value);
            for (var j=0;j<property.type().cardinality;++j) {
                PROTO.int32.SerializeToStream(wireId, stream);
                property.type().SerializeToStream(val[j], stream);
            }
        }
    }
};
PROTO.serializeProperty = function(property, stream, value) {
    var fid = property.id;
    if (!property.type()) return;
    if (property.type().cardinality>1) {
        PROTO.serializeTupleProperty(property,stream,value);
        return;
    }
    var wiretype = property.type().wiretype;
    var wireId = fid * 8 + wiretype;
//    PROTO.warn("Serializing property "+fid+" as "+wiretype+" pos is "+stream.write_pos_);
    if (property.multiplicity == PROTO.repeated) {
        if (wiretype != PROTO.wiretypes.lengthdelim && property.options.packed) {
            var bytearr = new Array();
            // Don't know length beforehand.
            var bas = new PROTO.ByteArrayStream(bytearr);
            for (var i = 0; i < value.length; i++) {
                var val = property.type().Convert(value[i]);
                property.type().SerializeToStream(val, bas);
            }
            wireId = fid * 8 + PROTO.wiretypes.lengthdelim;
            PROTO.int32.SerializeToStream(wireId, stream);
            PROTO.bytes.SerializeToStream(bytearr, stream);
        } else {
            for (var i = 0; i < value.length; i++) {
                PROTO.int32.SerializeToStream(wireId, stream);
                var val = property.type().Convert(value[i]);
                property.type().SerializeToStream(val, stream);
            }
        }
    } else {
        PROTO.int32.SerializeToStream(wireId, stream);
        var val = property.type().Convert(value);
        property.type().SerializeToStream(val, stream);
    }
};


PROTO.Message = function(name, properties) {
    /** @constructor */
    var Composite = function() {
        this.properties_ = Composite.properties_;
        if (!PROTO.DefineProperty) {
            this.values_ = this;
        } else {
            this.values_ = {};
        }
        this.Clear();
        this.message_type_ = name;
    };
    Composite.properties_ = {};
    for (var key in properties) {
        // HACK: classes are currently included alongside properties.
        if (properties[key].isType) {
            Composite[key] = properties[key];
        } else {
            Composite.properties_[key] = properties[key];
        }
    }
    Composite.isType = true;
    Composite.composite = true;
    Composite.wiretype = PROTO.wiretypes.lengthdelim;
    Composite.IsInitialized = function(value) {
        return value && value.IsInitialized();
    };
    Composite.Convert = function Convert(val) {
        if (!(val instanceof Composite)) {
            throw "Value not instanceof "+name+": "+typeof(val)+" : "+val;
        }
        return val;
    };
    Composite.SerializeToStream = function(value, stream) {
        var bytearr = new Array();
        var bas = new PROTO.ByteArrayStream(bytearr);
        value.SerializeToStream(bas);
        return PROTO.bytes.SerializeToStream(bytearr, stream);
    };
    Composite.ParseFromStream = function(stream) {
        var bytearr = PROTO.bytes.ParseFromStream(stream);
        var bas = PROTO.CreateArrayStream(bytearr);
        var ret = new Composite;
        ret.ParseFromStream(bas);
        return ret;
    };
    Composite.prototype = {
        computeHasFields: function computeHasFields() {
            var has_fields = {};
            for (var key in this.properties_) {
                if (this.HasField(key)) {
                    has_fields[key] = true;
                }
            }
            return has_fields;
        },
        Clear: function Clear() {
            for (var prop in this.properties_) {
                this.ClearField(prop);
            }
        },
        IsInitialized: function IsInitialized() {
            var checked_any = false;
            for (var key in this.properties_) {
                checked_any = true;
                if (this.values_[key] !== undefined) {
                    var descriptor = this.properties_[key];
                    if (!descriptor.type()) continue;
                    if (descriptor.multiplicity == PROTO.repeated) {
                        if (PROTO.array.IsInitialized(this.values_[key])) {
                            return true;
                        }
                    } else {
                        if (!descriptor.type().IsInitialized ||
                            descriptor.type().IsInitialized(this.values_[key]))
                        {
                            return true;
                        }
                    }
                }
            }
            // As a special case, if there weren't any fields, we
            // treat it as initialized. This allows us to send
            // messages that are empty, but whose presence indicates
            // something.
            if (!checked_any) return true;
            // Otherwise, we checked at least one and it failed, so we
            // must be uninitialized.
            return false;
        },
        ParseFromStream: function Parse(stream) {
            this.Clear();
            return this.MergeFromStream(stream);
        },
        MergeFromStream: function Merge(stream) {
            return PROTO.mergeProperties(this.properties_, stream, this.values_);
        },
        SerializeToStream: function Serialize(outstream) {
            var hasfields = this.computeHasFields();
            for (var key in hasfields) {
                var val = this.values_[key];
                PROTO.serializeProperty(this.properties_[key], outstream, val);
            }
        },
        SerializeToArray: function (opt_array) {
            var stream = new PROTO.ByteArrayStream(opt_array);
            this.SerializeToStream(stream);
            return stream.getArray();
        },
        MergeFromArray: function (array) {
            return this.MergeFromStream(PROTO.CreateArrayStream(array));
        },
        ParseFromArray: function (array) {
            this.Clear();
            return this.MergeFromArray(array);
        },
        // Not implemented:
        // CopyFrom, MergeFrom, SerializePartialToX,
        // RegisterExtension, Extensions, ClearExtension
        ClearField: function ClearField(propname) {
            var descriptor = this.properties_[propname];
            if (descriptor.multiplicity == PROTO.repeated) {
                this.values_[propname] = new PROTO.array(descriptor);
            } else {
                var type = descriptor.type();
                if (type && type.composite) {
                    // Don't special case this. Otherwise, we can't actually
                    // tell whether a composite child was initialized
                    // intentionally or if it just happened here.
                    //this.values_[propname] = new type();
                    delete this.values_[propname];
                } else {
                    delete this.values_[propname];
                }
            }
        },
        ListFields: function ListFields() {
            var ret = [];
            var hasfields = this.computeHasFields();
            for (var f in hasfields) {
                ret.push(f);
            }
            return ret;
        },
        GetField: function GetField(propname) {
            //PROTO.warn(propname);
            var ret = this.values_[propname];
            var type = this.properties_[propname].type();
            if (ret && type.FromProto) {
                return type.FromProto(ret);
            }
            return ret;
        },
        SetField: function SetField(propname, value) {
            //PROTO.warn(propname+"="+value);
            if (value === undefined || value === null) {
                this.ClearField(propname);
            } else {
                var prop = this.properties_[propname];
                if (prop.multiplicity == PROTO.repeated) {
                    this.ClearField(propname);
                    for (var i = 0; i < value.length; i++) {
                        this.values_[propname].push(
                                prop.type().Convert(value[i]));
                    }
                } else {
                    this.values_[propname] = prop.type().Convert(value);
                }
            }
        },
        HasField: function HasField(propname) {
            if (this.values_[propname] !== undefined) {
                var descriptor = this.properties_[propname];
                if (!descriptor.type()) {
                    return false;
                }
                if (descriptor.multiplicity == PROTO.repeated) {
                    return PROTO.array.IsInitialized(this.values_[propname]);
                } else {
                    if (!descriptor.type().IsInitialized ||
                        descriptor.type().IsInitialized(
                            this.values_[propname]))
                    {
                        return true;
                    }
                }
            }
            return false;
        },
        formatValue: function(level, spaces, propname, val) {
            var str = spaces + propname;
            var type = this.properties_[propname].type();
            if (type.composite) {
                str += " " + val.toString(level+1);
            } else if (typeof val == 'string') {
                var myval = val;
                myval = myval.replace("\"", "\\\"")
                             .replace("\n", "\\n")
                             .replace("\r","\\r");
                str += ": \"" + myval + "\"\n";
            } else {
                if (type.FromProto) {
                    val = type.FromProto(val);
                }
                if (type.toString) {
                    var myval = type.toString(val);
                    str += ": " + myval + "\n";
                } else {
                    str += ": " + val + "\n";
                }
            }
            return str;
        },
        toString: function toString(level) {
            var spaces = "";
            var str = "";
            if (level) {
                str = "{\n";
                for (var i = 0 ; i < level*2; i++) {
                    spaces += " ";
                }
            } else {
                level = 0;
            }
            for (var propname in this.properties_) {
                if (!this.properties_[propname].type()) {
                    continue; // HACK:
                }
                if (!this.HasField(propname)) {
                    continue;
                }
                if (this.properties_[propname].multiplicity == PROTO.repeated) {
                    var arr = this.values_[propname];
                    for (var i = 0; i < arr.length; i++) {
                        str += this.formatValue(level, spaces, propname, arr[i]);
                    }
                } else {
                    str += this.formatValue(level, spaces, propname,
                                            this.values_[propname]);
                }
            }
            if (level) {
                str += "}\n";
            }
            return str;
        }
    };
    if (PROTO.DefineProperty !== undefined) {
        for (var prop in Composite.properties_) {
            (function(prop){
            PROTO.DefineProperty(Composite.prototype, prop,
                           function GetProp() { return this.GetField(prop); },
                           function SetProp(newval) { this.SetField(prop, newval); });
            })(prop);
        }
    }
    return Composite;
};

/** Builds an enumeration type with a mapping of values.
@param {number=} bits  Preferred size of the enum (unused at the moment). */
PROTO.Enum = function (name, values, bits) {
    if (!bits) {
        bits = 32;
    }
    var reverseValues = {};
    var enumobj = {};
    enumobj.isType = true;
    for (var key in values) {
        reverseValues[values[key] ] = key;
        enumobj[key] = values[key];
        enumobj[values[key]] = key;
    }
    enumobj.values = values;
    enumobj.reverseValues = reverseValues;

    enumobj.Convert = function Convert(s) {
        if (typeof s == 'number') {
            // (reverseValues[s] !== undefined)
            return s;
        }
        if (values[s] !== undefined) {
            return values[s]; // Convert string -> int
        }
        throw "Not a valid "+name+" enumeration value: "+s;
    };
    enumobj.toString = function toString(num) {
        if (reverseValues[num]) {
            return reverseValues[num];
        }
        return "" + num;
    };
    enumobj.ParseFromStream = function(a,b) {
        var e = PROTO.int32.ParseFromStream(a,b);
        return e;
    }
    enumobj.SerializeToStream = function(a,b) {
        return PROTO.int32.SerializeToStream(a,b);
    }
    enumobj.wiretype = PROTO.wiretypes.varint;

    return enumobj;
};
PROTO.Flags = function(bits, name, values) {
    return PROTO.Enum(name, values, bits);
};

PROTO.Extend = function(parent, newproperties) {
    for (var key in newproperties) {
        parent.properties_[key] = newproperties[key];
    }
    return parent;
};

//////// DEBUG
if (typeof(self.console)=="undefined") self.console = {};
if (typeof(self.console.log)=="undefined") self.console.log = function(message){
    if (document && document.body)
        document.body.appendChild(document.createTextNode(message+"..."));
};
function serialize(message) {
	var stream = new PROTO.Base64Stream;
	message.SerializeToStream(stream);
	return {
			"type" : message.message_type_,
			"s" : stream.getString()
	};
}

function unserialize(message) {
	var msg;
	if (typeof(message) == "string")
		msg = JSON.parse(message);
	else
		msg = message.data;
	
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