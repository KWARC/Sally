using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Google.ProtocolBuffers;
using Cometd.Client;
using Cometd.Client.Transport;
using Cometd.Bayeux;
using Cometd.Bayeux.Client;
using Cometd.Common;

namespace ExcelAddIn1.Messaging
{
    /// <summary>
    /// Moving the messaging part to this namespace/folder to reorganize the project. Work suspended till higher priority issues are fixed.
    /// </summary>
    public class MessageParser : IMessageListener
    {

        public void onMessage(IClientSessionChannel session, Cometd.Bayeux.IMessage message)
        {

            Console.WriteLine(message);
            Google.ProtocolBuffers.IMessage msg = Util.restoreMessage(message);



        }
    }
}

