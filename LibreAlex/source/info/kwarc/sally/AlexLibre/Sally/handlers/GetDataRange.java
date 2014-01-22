package info.kwarc.sally.AlexLibre.Sally.handlers;

import info.kwarc.sally.AlexLibre.Sally.MessageHandler;
import info.kwarc.sally.AlexLibre.Sally.SallyManager;
import info.kwarc.sally.AlexLibre.Sally.SallyUtils;

import org.cometd.bayeux.client.ClientSessionChannel;

import sally.AlexRangeRequest;

import com.google.protobuf.AbstractMessage;
import com.sun.star.frame.XDesktop;
import com.sun.star.uno.XComponentContext;

public class GetDataRange implements MessageHandler {
	XComponentContext m_xContext;
	
	public GetDataRange() {

	}

	@Override
	public Object onMessage(ClientSessionChannel session, String channel,
			AbstractMessage msg) {
		
		if (!channel.equals("/get/data") || !(msg instanceof AlexRangeRequest))
			return null;
		
		m_xContext = SallyManager.getInstance().getContext();
		try {
			XDesktop desktop = SallyUtils.getDesktop(m_xContext);
			
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return null;
	}


}
