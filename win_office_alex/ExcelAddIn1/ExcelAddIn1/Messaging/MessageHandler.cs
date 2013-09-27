using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Cometd;
using Cometd.Bayeux.Client;
using Google.ProtocolBuffers;

namespace ExcelAddIn1.Messaging
{
    public interface MessageHandler
    {
        Object onMessage(IClientSessionChannel session, String channel, Cometd.Bayeux.IMessage msg);
    }
}
