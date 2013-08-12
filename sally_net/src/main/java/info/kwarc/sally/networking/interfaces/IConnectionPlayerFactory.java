package info.kwarc.sally.networking.interfaces;

import info.kwarc.sally.networking.ConnectionPlayer;

import java.io.Reader;

public interface IConnectionPlayerFactory {
	public ConnectionPlayer create(Reader inFile);
}
