/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class AFifoSend extends PSend
{
    private PVarref _varref_;
    private TBang _bang_;
    private PSendArgs _sendArgs_;

    public AFifoSend()
    {
        // Constructor
    }

    public AFifoSend(
        @SuppressWarnings("hiding") PVarref _varref_,
        @SuppressWarnings("hiding") TBang _bang_,
        @SuppressWarnings("hiding") PSendArgs _sendArgs_)
    {
        // Constructor
        setVarref(_varref_);

        setBang(_bang_);

        setSendArgs(_sendArgs_);

    }

    @Override
    public Object clone()
    {
        return new AFifoSend(
            cloneNode(this._varref_),
            cloneNode(this._bang_),
            cloneNode(this._sendArgs_));
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseAFifoSend(this);
    }

    public PVarref getVarref()
    {
        return this._varref_;
    }

    public void setVarref(PVarref node)
    {
        if(this._varref_ != null)
        {
            this._varref_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._varref_ = node;
    }

    public TBang getBang()
    {
        return this._bang_;
    }

    public void setBang(TBang node)
    {
        if(this._bang_ != null)
        {
            this._bang_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._bang_ = node;
    }

    public PSendArgs getSendArgs()
    {
        return this._sendArgs_;
    }

    public void setSendArgs(PSendArgs node)
    {
        if(this._sendArgs_ != null)
        {
            this._sendArgs_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._sendArgs_ = node;
    }

    @Override
    public String toString()
    {
        return ""
            + toString(this._varref_)
            + toString(this._bang_)
            + toString(this._sendArgs_);
    }

    @Override
    void removeChild(@SuppressWarnings("unused") Node child)
    {
        // Remove child
        if(this._varref_ == child)
        {
            this._varref_ = null;
            return;
        }

        if(this._bang_ == child)
        {
            this._bang_ = null;
            return;
        }

        if(this._sendArgs_ == child)
        {
            this._sendArgs_ = null;
            return;
        }

        throw new RuntimeException("Not a child.");
    }

    @Override
    void replaceChild(@SuppressWarnings("unused") Node oldChild, @SuppressWarnings("unused") Node newChild)
    {
        // Replace child
        if(this._varref_ == oldChild)
        {
            setVarref((PVarref) newChild);
            return;
        }

        if(this._bang_ == oldChild)
        {
            setBang((TBang) newChild);
            return;
        }

        if(this._sendArgs_ == oldChild)
        {
            setSendArgs((PSendArgs) newChild);
            return;
        }

        throw new RuntimeException("Not a child.");
    }
}
