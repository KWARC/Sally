package info.kwarc.sally.networking.interfaces;


public interface INetworkSenderAdapter {
	INetworkSender create(String clientID);
}
