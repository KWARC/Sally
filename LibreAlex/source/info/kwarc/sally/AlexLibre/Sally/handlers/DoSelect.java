package info.kwarc.sally.AlexLibre.Sally.handlers;

import info.kwarc.sally.AlexLibre.Sally.MessageHandler;
import info.kwarc.sally.AlexLibre.Sally.SallyManager;
import info.kwarc.sally.AlexLibre.Sally.SallyUtils;
import info.kwarc.sally.AlexLibre.Sally.SpreadsheetDoc;

import org.cometd.bayeux.client.ClientSessionChannel;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.AlexRangeRequest;

import com.google.protobuf.AbstractMessage;
import com.sun.star.frame.XDesktop;
import com.sun.star.uno.XComponentContext;

public class DoSelect implements MessageHandler {
	XComponentContext m_xContext;

	Logger log;
	public DoSelect() {
		log = LoggerFactory.getLogger(getClass());
	}

	@Override
	public Object onMessage(ClientSessionChannel session, String channel,
			AbstractMessage msg) {

		if (!channel.equals("/do/select") || !(msg instanceof AlexRangeRequest))
			return null;

		AlexRangeRequest request = (AlexRangeRequest) msg; 

		m_xContext = SallyManager.getInstance().getContext();
		try {
			SpreadsheetDoc doc = SallyManager.getInstance().getSpreadsheetDoc(request.getFileName());
			doc.selectRange(request.getSelectionList());
		} catch (Exception e) {
			log.error(e.getMessage());
			e.printStackTrace();
		}
		return null;

	}


}
