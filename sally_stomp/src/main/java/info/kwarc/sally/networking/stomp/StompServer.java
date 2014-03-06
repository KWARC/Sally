package info.kwarc.sally.networking.stomp;

import info.kwarc.sally.networking.IRequestHandler;

import javax.jms.Connection;
import javax.jms.Destination;
import javax.jms.JMSException;
import javax.jms.Message;
import javax.jms.MessageConsumer;
import javax.jms.MessageListener;
import javax.jms.MessageProducer;
import javax.jms.Session;
import javax.jms.TextMessage;

import org.eclipse.jetty.server.Handler;
import org.fusesource.stomp.jms.StompJmsConnectionFactory;
import org.fusesource.stomp.jms.StompJmsDestination;

public class StompServer  implements IRequestHandler {

	static class SimpleResponder implements MessageListener{
		Session session;
		
		public SimpleResponder(Session session) {
			this.session = session;
		}
		
		public void onMessage(Message msg) {
			try {
				System.out.println(msg.getJMSType());

				Destination r = msg.getJMSReplyTo();
				MessageProducer producer = session.createProducer(r);
				TextMessage message = session.createTextMessage("Okidoke");
				message.setJMSCorrelationID(msg.getJMSCorrelationID());
				producer.send(message);
			} catch (JMSException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
	}

	@Override
	public Handler onInit() {
        String user =  "admin";
        String password =  "password";
        String host =  "localhost";
        int port =  61613;
        String destination =  "/queue/sally_register";

        StompJmsConnectionFactory factory = new StompJmsConnectionFactory();
        factory.setBrokerURI("tcp://" + host + ":" + port);

		try {
		    Connection connection = factory.createConnection(user, password);
	        connection.start();
	        Session session = connection.createSession(false, Session.AUTO_ACKNOWLEDGE);
	        Destination dest = new StompJmsDestination(destination);

			MessageConsumer consumer = session.createConsumer(dest);
			consumer.setMessageListener(new SimpleResponder(session));

			Destination destination2 = session.createQueue("sally_getframes");
			MessageConsumer consumer2 = session.createConsumer(destination2);
			consumer2.setMessageListener(new SimpleResponder(session));

			Destination destination3 = session.createTopic("sally_what");
			MessageConsumer consumer3 = session.createConsumer(destination3);
			consumer3.setMessageListener(new SimpleResponder(session));

		} catch (JMSException e) {
			e.printStackTrace();
		}

		return null;
	}

	@Override
	public void onStart() {
		
	}

}
